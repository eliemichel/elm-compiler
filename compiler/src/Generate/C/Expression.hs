{-# LANGUAGE OverloadedStrings #-}
module Generate.C.Expression
  ( generate
  , generateCtor
  , generateField
  , generateTailDef
  , generateMain
  , Code
  , codeToExpr
  , codeToStmtList
  )
  where


import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.Map ((!))
import qualified Data.Map as Map
import qualified Data.Name as Name
import qualified Data.Set as Set
import qualified Data.Utf8 as Utf8

import qualified AST.Canonical as Can
import qualified AST.Optimized as Opt
import qualified AST.Utils.Shader as Shader
import qualified Data.Index as Index
import qualified Elm.Compiler.Type as Type
import qualified Elm.Compiler.Type.Extract as Extract
import qualified Elm.Version as V
import qualified Elm.ModuleName as ModuleName
import qualified Elm.Package as Pkg
import qualified Generate.C.Builder as C
import qualified Generate.C.Name as CName
import qualified Generate.Mode as Mode
import qualified Json.Encode as Encode
import Json.Encode ((==>))
import qualified Optimize.DecisionTree as DT
import qualified Reporting.Annotation as A



-- EXPRESSIONS


generateJsExpr :: Mode.Mode -> Opt.Expr -> C.Expr
generateJsExpr mode expression =
  codeToExpr (generate mode expression)


generate :: Mode.Mode -> Opt.Expr -> Code
generate mode expression =
  case expression of
    Opt.Bool bool ->
      JsExpr $ C.Bool bool

    Opt.Chr char ->
      JsExpr $
        case mode of
          Mode.Dev _ ->
            C.Call toChar [ C.String (Utf8.toBuilder char) ]

          Mode.Prod _ ->
            C.String (Utf8.toBuilder char)

    Opt.Str string ->
      JsExpr $ C.String (Utf8.toBuilder string)

    Opt.Int int ->
      JsExpr $ C.Int int

    Opt.Float float ->
      JsExpr $ C.Float (Utf8.toBuilder float)

    Opt.VarLocal name ->
      JsExpr $ C.Ref (CName.fromLocal name)

    Opt.VarGlobal (Opt.Global home name) ->
      JsExpr $ C.Ref (CName.fromGlobal home name)

    Opt.VarEnum (Opt.Global home name) index ->
      case mode of
        Mode.Dev _ ->
          JsExpr $ C.Ref (CName.fromGlobal home name)

        Mode.Prod _ ->
          JsExpr $ C.Int (Index.toMachine index)

    Opt.VarBox (Opt.Global home name) ->
      JsExpr $ C.Ref $
        case mode of
          Mode.Dev _ -> CName.fromGlobal home name
          Mode.Prod _ -> CName.fromGlobal ModuleName.basics Name.identity

    Opt.VarCycle home name ->
      JsExpr $ C.Call (C.Ref (CName.fromCycle home name)) []

    Opt.VarDebug name home region unhandledValueName ->
      JsExpr $ generateDebug name home region unhandledValueName

    Opt.VarKernel home name ->
      JsExpr $ C.Ref (CName.fromKernel home name)

    Opt.List entries ->
      case entries of
        [] ->
          JsExpr $ C.Ref (CName.fromKernel Name.list "Nil")

        _ ->
          JsExpr $
            C.Call
              (C.Ref (CName.fromKernel Name.list "fromArray"))
              [ C.Array $ map (generateJsExpr mode) entries
              ]

    Opt.Function args body ->
      generateFunction (map CName.fromLocal args) (generate mode body)

    Opt.Call func args ->
      JsExpr $ generateCall mode func args

    Opt.TailCall name args ->
      JsBlock $ generateTailCall mode name args

    Opt.If branches final ->
      generateIf mode branches final

    Opt.Let def body ->
      JsBlock $
        generateDef mode def : codeToStmtList (generate mode body)

    Opt.Destruct (Opt.Destructor name path) body ->
      let
        pathDef = C.Var (CName.fromLocal "PATH_TYPE") (CName.fromLocal name) (generatePath mode path)
      in
      JsBlock $ pathDef : codeToStmtList (generate mode body)

    Opt.Case label root decider jumps ->
      JsBlock $ generateCase mode label root decider jumps

    Opt.Accessor field ->
      JsExpr $ C.Function Nothing [CName.dollar]
        [ C.Return $
            C.Access (C.Ref CName.dollar) (generateField mode field)
        ]

    Opt.Access record field ->
      JsExpr $ C.Access (generateJsExpr mode record) (generateField mode field)

    Opt.Update record fields ->
      JsExpr $
        C.Call (C.Ref (CName.fromKernel Name.utils "update"))
          [ generateJsExpr mode record
          , generateRecord mode fields
          ]

    Opt.Record fields ->
      JsExpr $ generateRecord mode fields

    Opt.Unit ->
      case mode of
        Mode.Dev _ ->
          JsExpr $ C.Ref (CName.fromKernel Name.utils "Tuple0")

        Mode.Prod _ ->
          JsExpr $ C.Int 0

    Opt.Tuple a b maybeC ->
      JsExpr $
        case maybeC of
          Nothing ->
            C.Call (C.Ref (CName.fromKernel Name.utils "Tuple2"))
              [ generateJsExpr mode a
              , generateJsExpr mode b
              ]

          Just c ->
            C.Call (C.Ref (CName.fromKernel Name.utils "Tuple3"))
              [ generateJsExpr mode a
              , generateJsExpr mode b
              , generateJsExpr mode c
              ]

    Opt.Shader src attributes uniforms ->
      let
        toTranlation field =
          ( CName.fromLocal field
          , C.String (CName.toBuilder (generateField mode field))
          )

        toTranslationObject fields =
          C.Object (map toTranlation (Set.toList fields))
      in
      JsExpr $ C.Object $
        [ ( CName.fromLocal "src", C.String (Shader.toJsStringBuilder src) )
        , ( CName.fromLocal "attributes", toTranslationObject attributes )
        , ( CName.fromLocal "uniforms", toTranslationObject uniforms )
        ]



-- CODE CHUNKS


data Code
    = JsExpr C.Expr
    | JsBlock [C.Stmt]


codeToExpr :: Code -> C.Expr
codeToExpr code =
  case code of
    JsExpr expr ->
      expr

    JsBlock [ C.Return expr ] ->
      expr

    JsBlock stmts ->
      C.Call (C.Function Nothing [] stmts) []


codeToStmtList :: Code -> [C.Stmt]
codeToStmtList code =
  case code of
    JsExpr (C.Call (C.Function Nothing [] stmts) []) ->
        stmts

    JsExpr expr ->
        [ C.Return expr ]

    JsBlock stmts ->
        stmts


codeToStmt :: Code -> C.Stmt
codeToStmt code =
  case code of
    JsExpr (C.Call (C.Function Nothing [] stmts) []) ->
        C.Block stmts

    JsExpr expr ->
        C.Return expr

    JsBlock [stmt] ->
        stmt

    JsBlock stmts ->
        C.Block stmts



-- CHARS


{-# NOINLINE toChar #-}
toChar :: C.Expr
toChar =
  C.Ref (CName.fromKernel Name.utils "chr")



-- CTOR


generateCtor :: Mode.Mode -> Opt.Global -> Index.ZeroBased -> Int -> Code
generateCtor mode (Opt.Global home name) index arity =
  let
    argNames =
      Index.indexedMap (\i _ -> CName.fromIndex i) [1 .. arity]

    ctorTag =
      case mode of
        Mode.Dev _ -> C.String (Name.toBuilder name)
        Mode.Prod _ -> C.Int (ctorToInt home name index)
  in
  generateFunction argNames $ JsExpr $ C.Object $
    (CName.dollar, ctorTag) : map (\n -> (n, C.Ref n)) argNames


ctorToInt :: ModuleName.Canonical -> Name.Name -> Index.ZeroBased -> Int
ctorToInt home name index =
  if home == ModuleName.dict && name == "RBNode_elm_builtin" || name == "RBEmpty_elm_builtin" then
    0 - Index.toHuman index
  else
    Index.toMachine index



-- RECORDS


generateRecord :: Mode.Mode -> Map.Map Name.Name Opt.Expr -> C.Expr
generateRecord mode fields =
  let
    toPair (field, value) =
      (generateField mode field, generateJsExpr mode value)
  in
  C.Object (map toPair (Map.toList fields))


generateField :: Mode.Mode -> Name.Name -> CName.Name
generateField mode name =
  case mode of
    Mode.Dev _ ->
      CName.fromLocal name

    Mode.Prod fields ->
      Mode.getFieldCName fields name




-- DEBUG


generateDebug :: Name.Name -> ModuleName.Canonical -> A.Region -> Maybe Name.Name -> C.Expr
generateDebug name (ModuleName.Canonical _ home) region unhandledValueName =
  if name /= "todo" then
    C.Ref (CName.fromGlobal ModuleName.debug name)
  else
    case unhandledValueName of
      Nothing ->
        C.Call (C.Ref (CName.fromKernel Name.debug "todo")) $
          [ C.String (Name.toBuilder home)
          , regionToJsExpr region
          ]

      Just valueName ->
        C.Call (C.Ref (CName.fromKernel Name.debug "todoCase")) $
          [ C.String (Name.toBuilder home)
          , regionToJsExpr region
          , C.Ref (CName.fromLocal valueName)
          ]


regionToJsExpr :: A.Region -> C.Expr
regionToJsExpr (A.Region start end) =
  C.Object
    [ ( CName.fromLocal "start", positionToJsExpr start )
    , ( CName.fromLocal "end", positionToJsExpr end )
    ]


positionToJsExpr :: A.Position -> C.Expr
positionToJsExpr (A.Position line column) =
  C.Object
    [ ( CName.fromLocal "line", C.Int (fromIntegral line) )
    , ( CName.fromLocal "column", C.Int (fromIntegral column) )
    ]



-- FUNCTION


generateFunction :: [CName.Name] -> Code -> Code
generateFunction args body =
  case IntMap.lookup (length args) funcHelpers of
    Just helper ->
      JsExpr $
        C.Call helper
          [ C.Function Nothing args $
              codeToStmtList body
          ]

    Nothing ->
      let
        addArg arg code =
          JsExpr $ C.Function Nothing [arg] $
            codeToStmtList code
      in
      foldr addArg body args


{-# NOINLINE funcHelpers #-}
funcHelpers :: IntMap.IntMap C.Expr
funcHelpers =
  IntMap.fromList $
    map (\n -> (n, C.Ref (CName.makeF n))) [2..9]



-- CALLS


generateCall :: Mode.Mode -> Opt.Expr -> [Opt.Expr] -> C.Expr
generateCall mode func args =
  case func of
    Opt.VarGlobal global@(Opt.Global (ModuleName.Canonical pkg _) _) | pkg == Pkg.core ->
      generateCoreCall mode global args

    Opt.VarBox _ ->
      case mode of
        Mode.Dev _ ->
          generateCallHelp mode func args

        Mode.Prod _ ->
          case args of
            [arg] ->
              generateJsExpr mode arg

            _ ->
              generateCallHelp mode func args

    _ ->
      generateCallHelp mode func args


generateCallHelp :: Mode.Mode -> Opt.Expr -> [Opt.Expr] -> C.Expr
generateCallHelp mode func args =
  generateNormalCall
    (generateJsExpr mode func)
    (map (generateJsExpr mode) args)


generateGlobalCall :: ModuleName.Canonical -> Name.Name -> [C.Expr] -> C.Expr
generateGlobalCall home name args =
  generateNormalCall (C.Ref (CName.fromGlobal home name)) args


generateNormalCall :: C.Expr -> [C.Expr] -> C.Expr
generateNormalCall func args =
  case IntMap.lookup (length args) callHelpers of
    Just helper ->
      C.Call helper (func:args)

    Nothing ->
      List.foldl' (\f a -> C.Call f [a]) func args


{-# NOINLINE callHelpers #-}
callHelpers :: IntMap.IntMap C.Expr
callHelpers =
  IntMap.fromList $
    map (\n -> (n, C.Ref (CName.makeA n))) [2..9]



-- CORE CALLS


generateCoreCall :: Mode.Mode -> Opt.Global -> [Opt.Expr] -> C.Expr
generateCoreCall mode (Opt.Global home@(ModuleName.Canonical _ moduleName) name) args =
  if moduleName == Name.basics then
    generateBasicsCall mode home name args

  else if moduleName == Name.bitwise then
    generateBitwiseCall home name (map (generateJsExpr mode) args)

  else if moduleName == Name.tuple then
    generateTupleCall home name (map (generateJsExpr mode) args)

  else if moduleName == Name.jsArray then
    generateJsArrayCall home name (map (generateJsExpr mode) args)

  else
    generateGlobalCall home name (map (generateJsExpr mode) args)


generateTupleCall :: ModuleName.Canonical -> Name.Name -> [C.Expr] -> C.Expr
generateTupleCall home name args =
  case args of
    [value] ->
      case name of
        "first"  -> C.Access value (CName.fromLocal "a")
        "second" -> C.Access value (CName.fromLocal "b")
        _        -> generateGlobalCall home name args

    _ ->
      generateGlobalCall home name args


generateJsArrayCall :: ModuleName.Canonical -> Name.Name -> [C.Expr] -> C.Expr
generateJsArrayCall home name args =
  case args of
    [entry]        | name == "singleton" -> C.Array [entry]
    [index, array] | name == "unsafeGet" -> C.Index array index
    _                                    -> generateGlobalCall home name args


generateBitwiseCall :: ModuleName.Canonical -> Name.Name -> [C.Expr] -> C.Expr
generateBitwiseCall home name args =
  case args of
    [arg] ->
      case name of
        "complement" -> C.Prefix C.PrefixComplement arg
        _            -> generateGlobalCall home name args

    [left,right] ->
      case name of
        "and"            -> C.Infix C.OpBitwiseAnd left right
        "or"             -> C.Infix C.OpBitwiseOr  left right
        "xor"            -> C.Infix C.OpBitwiseXor left right
        "shiftLeftBy"    -> C.Infix C.OpLShift     right left
        "shiftRightBy"   -> C.Infix C.OpSpRShift   right left
        "shiftRightZfBy" -> C.Infix C.OpZfRShift   right left
        _                -> generateGlobalCall home name args

    _ ->
      generateGlobalCall home name args


generateBasicsCall :: Mode.Mode -> ModuleName.Canonical -> Name.Name -> [Opt.Expr] -> C.Expr
generateBasicsCall mode home name args =
  case args of
    [elmArg] ->
      let arg = generateJsExpr mode elmArg in
      case name of
        "not"      -> C.Prefix C.PrefixNot arg
        "negate"   -> C.Prefix C.PrefixNegate arg
        "toFloat"  -> arg
        "truncate" -> C.Infix C.OpBitwiseOr arg (C.Int 0)
        _          -> generateGlobalCall home name [arg]

    [elmLeft, elmRight] ->
      case name of
        -- NOTE: removed "composeL" and "composeR" because of this issue:
        -- https://github.com/elm/compiler/issues/1722
        "append"   -> append mode elmLeft elmRight
        "apL"      -> generateJsExpr mode $ apply elmLeft elmRight
        "apR"      -> generateJsExpr mode $ apply elmRight elmLeft
        _ ->
          let
            left = generateJsExpr mode elmLeft
            right = generateJsExpr mode elmRight
          in
          case name of
            "add"  -> C.Infix C.OpAdd left right
            "sub"  -> C.Infix C.OpSub left right
            "mul"  -> C.Infix C.OpMul left right
            "fdiv" -> C.Infix C.OpDiv left right
            "idiv" -> C.Infix C.OpBitwiseOr (C.Infix C.OpDiv left right) (C.Int 0)
            "eq"   -> equal left right
            "neq"  -> notEqual left right
            "lt"   -> cmp C.OpLt C.OpLt   0  left right
            "gt"   -> cmp C.OpGt C.OpGt   0  left right
            "le"   -> cmp C.OpLe C.OpLt   1  left right
            "ge"   -> cmp C.OpGe C.OpGt (-1) left right
            "or"   -> C.Infix C.OpOr  left right
            "and"  -> C.Infix C.OpAnd left right
            "xor"  -> C.Infix C.OpNe  left right
            "remainderBy" -> C.Infix C.OpMod right left
            _      -> generateGlobalCall home name [left, right]

    _ ->
      generateGlobalCall home name (map (generateJsExpr mode) args)


equal :: C.Expr -> C.Expr -> C.Expr
equal left right =
  if isLiteral left || isLiteral right then
    strictEq left right
  else
    C.Call (C.Ref (CName.fromKernel Name.utils "eq")) [left, right]


notEqual :: C.Expr -> C.Expr -> C.Expr
notEqual left right =
  if isLiteral left || isLiteral right then
    strictNEq left right
  else
    C.Prefix C.PrefixNot $
      C.Call (C.Ref (CName.fromKernel Name.utils "eq")) [left, right]


cmp :: C.InfixOp -> C.InfixOp -> Int -> C.Expr -> C.Expr -> C.Expr
cmp idealOp backupOp backupInt left right =
  if isLiteral left || isLiteral right then
    C.Infix idealOp left right
  else
    C.Infix backupOp
      (C.Call (C.Ref (CName.fromKernel Name.utils "cmp")) [left, right])
      (C.Int backupInt)


isLiteral :: C.Expr -> Bool
isLiteral expr =
  case expr of
    C.String _ ->
      True

    C.Float _ ->
      True

    C.Int _ ->
      True

    C.Bool _ ->
      True

    _ ->
      False


apply :: Opt.Expr -> Opt.Expr -> Opt.Expr
apply func value =
  case func of
    Opt.Accessor field ->
      Opt.Access value field

    Opt.Call f args ->
      Opt.Call f (args ++ [value])

    _ ->
      Opt.Call func [value]


append :: Mode.Mode -> Opt.Expr -> Opt.Expr -> C.Expr
append mode left right =
  let seqs = generateJsExpr mode left : toSeqs mode right in
  if any isStringLiteral seqs then
    foldr1 (C.Infix C.OpAdd) seqs
  else
    foldr1 jsAppend seqs


jsAppend :: C.Expr -> C.Expr -> C.Expr
jsAppend a b =
  C.Call (C.Ref (CName.fromKernel Name.utils "ap")) [a, b]


toSeqs :: Mode.Mode -> Opt.Expr -> [C.Expr]
toSeqs mode expr =
  case expr of
    Opt.Call (Opt.VarGlobal (Opt.Global home "append")) [left, right]
      | home == ModuleName.basics ->
          generateJsExpr mode left : toSeqs mode right

    _ ->
      [generateJsExpr mode expr]


isStringLiteral :: C.Expr -> Bool
isStringLiteral expr =
  case expr of
    C.String _ ->
      True

    _ ->
      False



-- SIMPLIFY INFIX OPERATORS


strictEq :: C.Expr -> C.Expr -> C.Expr
strictEq left right =
  case left of
    C.Int 0 ->
      C.Prefix C.PrefixNot right

    C.Bool bool ->
      if bool then right else C.Prefix C.PrefixNot right

    _ ->
      case right of
        C.Int 0 ->
          C.Prefix C.PrefixNot left

        C.Bool bool ->
          if bool then left else C.Prefix C.PrefixNot left

        _ ->
          C.Infix C.OpEq left right


strictNEq :: C.Expr -> C.Expr -> C.Expr
strictNEq left right =
  case left of
    C.Int 0 ->
      C.Prefix C.PrefixNot (C.Prefix C.PrefixNot right)

    C.Bool bool ->
      if bool then C.Prefix C.PrefixNot right else right

    _ ->
      case right of
        C.Int 0 ->
          C.Prefix C.PrefixNot (C.Prefix C.PrefixNot left)

        C.Bool bool ->
          if bool then C.Prefix C.PrefixNot left else left

        _ ->
          C.Infix C.OpNe left right



-- TAIL CALL


-- TODO check if JS minifiers collapse unnecessary temporary variables
--
generateTailCall :: Mode.Mode -> Name.Name -> [(Name.Name, Opt.Expr)] -> [C.Stmt]
generateTailCall mode name args =
  let
    toTempVars (argName, arg) =
      ( CName.makeTemp argName, generateJsExpr mode arg )

    toRealVars (argName, _) =
      C.ExprStmt $
        C.Assign (C.LRef (CName.fromLocal argName)) (C.Ref (CName.makeTemp argName))
  in
  C.Vars (CName.fromLocal "TAIL_CALL_TYPE") (map toTempVars args)
  : map toRealVars args
  ++ [ C.Continue (Just (CName.fromLocal name)) ]



-- DEFINITIONS


generateDef :: Mode.Mode -> Opt.Def -> C.Stmt
generateDef mode def =
  case def of
    Opt.Def name body ->
      C.Var (CName.fromLocal "DEF_TYPE") (CName.fromLocal name) (generateJsExpr mode body)

    Opt.TailDef name argNames body ->
      C.Var (CName.fromLocal "TAIL_DEF_TYPE") (CName.fromLocal name) (codeToExpr (generateTailDef mode name argNames body))


generateTailDef :: Mode.Mode -> Name.Name -> [Name.Name] -> Opt.Expr -> Code
generateTailDef mode name argNames body =
  generateFunction (map CName.fromLocal argNames) $ JsBlock $
    [ C.Labelled (CName.fromLocal name) $
        C.While (C.Bool True) $
          codeToStmt $ generate mode body
    ]



-- PATHS


generatePath :: Mode.Mode -> Opt.Path -> C.Expr
generatePath mode path =
  case path of
    Opt.Index index subPath ->
      C.Access (generatePath mode subPath) (CName.fromIndex index)

    Opt.Root name ->
      C.Ref (CName.fromLocal name)

    Opt.Field field subPath ->
      C.Access (generatePath mode subPath) (generateField mode field)

    Opt.Unbox subPath ->
      case mode of
        Mode.Dev _ ->
          C.Access (generatePath mode subPath) (CName.fromIndex Index.first)

        Mode.Prod _ ->
          generatePath mode subPath



-- GENERATE IFS


generateIf :: Mode.Mode -> [(Opt.Expr, Opt.Expr)] -> Opt.Expr -> Code
generateIf mode givenBranches givenFinal =
  let
    (branches, final) =
      crushIfs givenBranches givenFinal

    convertBranch (condition, expr) =
      ( generateJsExpr mode condition
      , generate mode expr
      )

    branchExprs = map convertBranch branches
    finalCode = generate mode final
  in
  if isBlock finalCode || any (isBlock . snd) branchExprs then
    JsBlock [ foldr addStmtIf (codeToStmt finalCode) branchExprs ]
  else
    JsExpr $ foldr addExprIf (codeToExpr finalCode) branchExprs


addExprIf :: (C.Expr, Code) -> C.Expr -> C.Expr
addExprIf (condition, branch) final =
  C.If condition (codeToExpr branch) final


addStmtIf :: (C.Expr, Code) -> C.Stmt -> C.Stmt
addStmtIf (condition, branch) final =
  C.IfStmt condition (codeToStmt branch) final


isBlock :: Code -> Bool
isBlock code =
  case code of
    JsBlock _ -> True
    JsExpr _ -> False


crushIfs :: [(Opt.Expr, Opt.Expr)] -> Opt.Expr -> ([(Opt.Expr, Opt.Expr)], Opt.Expr)
crushIfs branches final =
  crushIfsHelp [] branches final


crushIfsHelp
    :: [(Opt.Expr, Opt.Expr)]
    -> [(Opt.Expr, Opt.Expr)]
    -> Opt.Expr
    -> ([(Opt.Expr, Opt.Expr)], Opt.Expr)
crushIfsHelp visitedBranches unvisitedBranches final =
  case unvisitedBranches of
    [] ->
        case final of
          Opt.If subBranches subFinal ->
              crushIfsHelp visitedBranches subBranches subFinal

          _ ->
              (reverse visitedBranches, final)

    visiting : unvisited ->
        crushIfsHelp (visiting : visitedBranches) unvisited final



-- CASE EXPRESSIONS


generateCase :: Mode.Mode -> Name.Name -> Name.Name -> Opt.Decider Opt.Choice -> [(Int, Opt.Expr)] -> [C.Stmt]
generateCase mode label root decider jumps =
  foldr (goto mode label) (generateDecider mode label root decider) jumps


goto :: Mode.Mode -> Name.Name -> (Int, Opt.Expr) -> [C.Stmt] -> [C.Stmt]
goto mode label (index, branch) stmts =
  let
    labeledDeciderStmt =
      C.Labelled
        (CName.makeLabel label index)
        (C.While (C.Bool True) (C.Block stmts))
  in
  labeledDeciderStmt : codeToStmtList (generate mode branch)


generateDecider :: Mode.Mode -> Name.Name -> Name.Name -> Opt.Decider Opt.Choice -> [C.Stmt]
generateDecider mode label root decisionTree =
  case decisionTree of
    Opt.Leaf (Opt.Inline branch) ->
      codeToStmtList (generate mode branch)

    Opt.Leaf (Opt.Jump index) ->
      [ C.Break (Just (CName.makeLabel label index)) ]

    Opt.Chain testChain success failure ->
      [ C.IfStmt
          (List.foldl1' (C.Infix C.OpAnd) (map (generateIfTest mode root) testChain))
          (C.Block $ generateDecider mode label root success)
          (C.Block $ generateDecider mode label root failure)
      ]

    Opt.FanOut path edges fallback ->
      [ C.Switch
          (generateCaseTest mode root path (fst (head edges)))
          ( foldr
              (\edge cases -> generateCaseBranch mode label root edge : cases)
              [ C.Default (generateDecider mode label root fallback) ]
              edges
          )
      ]


generateIfTest :: Mode.Mode -> Name.Name -> (DT.Path, DT.Test) -> C.Expr
generateIfTest mode root (path, test) =
  let
    value = pathToJsExpr mode root path
  in
  case test of
    DT.IsCtor home name index _ opts ->
      let
        tag =
          case mode of
            Mode.Dev _ -> C.Access value CName.dollar
            Mode.Prod _ ->
              case opts of
                Can.Normal -> C.Access value CName.dollar
                Can.Enum   -> value
                Can.Unbox  -> value
      in
      strictEq tag $
        case mode of
          Mode.Dev _ -> C.String (Name.toBuilder name)
          Mode.Prod _ -> C.Int (ctorToInt home name index)

    DT.IsBool True ->
      value

    DT.IsBool False ->
      C.Prefix C.PrefixNot value

    DT.IsInt int ->
      strictEq value (C.Int int)

    DT.IsChr char ->
      strictEq (C.String (Utf8.toBuilder char)) $
        case mode of
          Mode.Dev _ -> C.Call (C.Access value (CName.fromLocal "valueOf")) []
          Mode.Prod _ -> value

    DT.IsStr string ->
      strictEq value (C.String (Utf8.toBuilder string))

    DT.IsCons ->
      C.Access value (CName.fromLocal "b")

    DT.IsNil ->
      C.Prefix C.PrefixNot $
        C.Access value (CName.fromLocal "b")

    DT.IsTuple ->
      error "COMPILER BUG - there should never be tests on a tuple"



generateCaseBranch :: Mode.Mode -> Name.Name -> Name.Name -> (DT.Test, Opt.Decider Opt.Choice) -> C.Case
generateCaseBranch mode label root (test, subTree) =
  C.Case
    (generateCaseValue mode test)
    (generateDecider mode label root subTree)


generateCaseValue :: Mode.Mode -> DT.Test -> C.Expr
generateCaseValue mode test =
  case test of
    DT.IsCtor home name index _ _ ->
      case mode of
        Mode.Dev _ -> C.String (Name.toBuilder name)
        Mode.Prod _ -> C.Int (ctorToInt home name index)

    DT.IsInt int ->
      C.Int int

    DT.IsChr char ->
      C.String (Utf8.toBuilder char)

    DT.IsStr string ->
      C.String (Utf8.toBuilder string)

    DT.IsBool _ ->
      error "COMPILER BUG - there should never be three tests on a boolean"

    DT.IsCons ->
      error "COMPILER BUG - there should never be three tests on a list"

    DT.IsNil ->
      error "COMPILER BUG - there should never be three tests on a list"

    DT.IsTuple ->
      error "COMPILER BUG - there should never be three tests on a tuple"


generateCaseTest :: Mode.Mode -> Name.Name -> DT.Path -> DT.Test -> C.Expr
generateCaseTest mode root path exampleTest =
  let
    value = pathToJsExpr mode root path
  in
  case exampleTest of
    DT.IsCtor home name _ _ opts ->
      if name == Name.bool && home == ModuleName.basics then
        value
      else
        case mode of
          Mode.Dev _ ->
            C.Access value CName.dollar

          Mode.Prod _ ->
            case opts of
              Can.Normal ->
                C.Access value CName.dollar

              Can.Enum ->
                value

              Can.Unbox ->
                value

    DT.IsInt _ ->
      value

    DT.IsStr _ ->
      value

    DT.IsChr _ ->
      case mode of
        Mode.Dev _ ->
          C.Call (C.Access value (CName.fromLocal "valueOf")) []

        Mode.Prod _ ->
          value

    DT.IsBool _ ->
      error "COMPILER BUG - there should never be three tests on a list"

    DT.IsCons ->
      error "COMPILER BUG - there should never be three tests on a list"

    DT.IsNil ->
      error "COMPILER BUG - there should never be three tests on a list"

    DT.IsTuple ->
      error "COMPILER BUG - there should never be three tests on a list"



-- PATTERN PATHS


pathToJsExpr :: Mode.Mode -> Name.Name -> DT.Path -> C.Expr
pathToJsExpr mode root path =
  case path of
    DT.Index index subPath ->
      C.Access (pathToJsExpr mode root subPath) (CName.fromIndex index)

    DT.Unbox subPath ->
      case mode of
        Mode.Dev _ ->
          C.Access (pathToJsExpr mode root subPath) (CName.fromIndex Index.first)

        Mode.Prod _ ->
          pathToJsExpr mode root subPath

    DT.Empty ->
      C.Ref (CName.fromLocal root)



-- GENERATE MAIN


generateMain :: Mode.Mode -> ModuleName.Canonical -> Opt.Main -> C.Expr
generateMain mode home main =
  case main of
    Opt.Static ->
      C.Ref (CName.fromKernel Name.virtualDom "init")
        # C.Ref (CName.fromGlobal home "main")
        # C.Int 0
        # C.Int 0

    Opt.Dynamic msgType decoder ->
      C.Ref (CName.fromGlobal home "main")
        # generateJsExpr mode decoder
        # toDebugMetadata mode msgType


(#) :: C.Expr -> C.Expr -> C.Expr
(#) func arg =
  C.Call func [arg]


toDebugMetadata :: Mode.Mode -> Can.Type -> C.Expr
toDebugMetadata mode msgType =
  case mode of
    Mode.Prod _ ->
      C.Int 0

    Mode.Dev Nothing ->
      C.Int 0

    Mode.Dev (Just interfaces) ->
      C.Json $ Encode.object $
        [ "versions" ==> Encode.object [ "elm" ==> V.encode V.compiler ]
        , "types"    ==> Type.encodeMetadata (Extract.fromMsg interfaces msgType)
        ]
