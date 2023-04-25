include "peval/include.mc" 
include "peval/ast.mc"

include "mexpr/utils.mc"
include "mexpr/pprint.mc"
include "mexpr/extract.mc"
include "mexpr/ast.mc"

include "set.mc"


lang PEvalUtils = PEvalAst + PEvalInclude + MExprPrettyPrint + MExprExtract + LamAst 

  type PEvalNames = {
    pevalNames : Map String Name,
    consNames : Map String Name,
    builtinsNames : Map String Name,
    tyConsNames : Map String Name,
    otherFuncs : Map String Name
  }

  type PEvalArgs = {
    lib : Map Name Expr,
    -- For each binding in the reclet, store the name of the other bindings
    -- and the binding itself
    rlMapping: Map Name ([Name], RecLetBinding),
    idMapping : Map Name Name,
    closing : Bool
  }
  sem initArgs : () -> PEvalArgs
  sem initArgs = | _ -> {lib = (mapEmpty nameCmp), 
                   rlMapping = (mapEmpty nameCmp),
                   closing=false, idMapping= (mapEmpty nameCmp)}

  sem updateLib : PEvalArgs -> Map Name Expr -> PEvalArgs
  sem updateLib args = | lib -> {args with lib = lib}

  sem updateRlMapping : PEvalArgs -> Map Name ([Name], RecLetBinding)
                        -> PEvalArgs
  sem updateRlMapping args = | lib -> {args with rlMapping = lib}

  sem updateIds : PEvalArgs -> Map Name Name -> PEvalArgs
  sem updateIds args = | idm -> {args with idMapping =idm}

  sem updateClosing : PEvalArgs -> Bool -> PEvalArgs
  sem updateClosing args = | b -> {args with closing = b}

  sem isClosing : PEvalArgs -> Bool
  sem isClosing = | args -> args.closing

  sem _nameSeqToMap : [Name] -> Map String Name
  sem _nameSeqToMap = | names ->
  mapFromSeq cmpString (map (lam name. (name.0, name)) names)

  sem findNames : Expr -> [String] -> Map String Name 
  sem findNames ast = | includes ->
  let names = filterOption (findNamesOfStrings includes ast) in
  if eqi (length includes) (length names) then
    _nameSeqToMap names 
  else 
    error "A necessary include could not be found in the AST"

  sem createNames : Expr -> [Name] -> PEvalNames
  sem createNames ast =
  | pevalNames ->
  let pevalNames = _nameSeqToMap pevalNames in
  let consNames = findNames ast includeConsNames in
  let builtinsNames = findNames ast includeBuiltins in
  let tyConsNames = findNames ast includeTyConsNames in
  let otherFuncs = findNames ast otherFuncs in
  {pevalNames = pevalNames, 
   consNames = consNames,
   builtinsNames = builtinsNames, 
   tyConsNames = tyConsNames,
   otherFuncs=otherFuncs}

  sem getName : Map String Name -> String -> Name
  sem getName names =
  | str -> match mapLookup str names with Some n then n
           else error (concat "Could not find: " str) 

  sem pevalName : PEvalNames -> Name
  sem pevalName = | names -> getName (names.pevalNames) "pevalWithEnv"

  sem tmClosName : PEvalNames -> Name
  sem tmClosName = | names -> getName (names.consNames) "ClosAst_TmClos"

  sem tmAppName : PEvalNames -> Name
  sem tmAppName = | names -> getName (names.consNames) "AppAst_TmApp"

  sem tmLamName : PEvalNames -> Name
  sem tmLamName = | names -> getName (names.consNames) "LamAst_TmLam"

  sem tmVarName : PEvalNames -> Name
  sem tmVarName = | names -> getName (names.consNames) "VarAst_TmVar"

  sem tmRecName : PEvalNames -> Name
  sem tmRecName = | names -> getName (names.consNames) "RecordAst_TmRecord"

  sem tmSeqName : PEvalNames -> Name
  sem tmSeqName = | names -> getName (names.consNames) "SeqAst_TmSeq"

  sem tmConstName : PEvalNames -> Name
  sem tmConstName = | names -> getName (names.consNames) "ConstAst_TmConst"

  sem tmMatchName : PEvalNames -> Name
  sem tmMatchName = | names -> getName (names.consNames) "MatchAst_TmMatch"

  sem tmLetName : PEvalNames -> Name
  sem tmLetName = | names -> getName (names.consNames) "LetAst_TmLet"

  sem listConsName : PEvalNames -> Name
  sem listConsName = | names -> getName (names.consNames) "Cons"

  sem listNilName : PEvalNames -> Name
  sem listNilName = | names -> getName (names.consNames) "Nil"

  sem infoName : PEvalNames -> Name
  sem infoName = | names -> getName (names.consNames) "Info"

  sem noInfoName : PEvalNames -> Name
  sem noInfoName = | names -> getName (names.consNames) "NoInfo"

  sem tyAppName : PEvalNames -> Name
  sem tyAppName = | names -> getName (names.tyConsNames) "AppTypeAst_TyApp"

  sem tyVarName : PEvalNames -> Name
  sem tyVarName = | names -> getName (names.tyConsNames) "VarTypeAst_TyVar"

  sem tyIntName : PEvalNames -> Name
  sem tyIntName = | names -> getName (names.tyConsNames) "IntTypeAst_TyInt"

  sem tyBoolName : PEvalNames -> Name
  sem tyBoolName = | names -> getName (names.tyConsNames) "BoolTypeAst_TyBool"

  sem tyFloatName : PEvalNames -> Name
  sem tyFloatName = | names -> getName (names.tyConsNames) "FloatTypeAst_TyFloat"

  sem tyCharName : PEvalNames -> Name
  sem tyCharName = | names -> getName (names.tyConsNames) "CharTypeAst_TyChar"

  sem tyUnknownName : PEvalNames -> Name
  sem tyUnknownName = | names -> getName (names.tyConsNames) "UnknownTypeAst_TyUnknown"

  sem tyArrowName : PEvalNames -> Name
  sem tyArrowName = | names -> getName (names.tyConsNames) "FunTypeAst_TyArrow"

  sem mapFromSeqName : PEvalNames -> Name
  sem mapFromSeqName = | names -> getName (names.otherFuncs) "mapFromSeq"

  sem mapToSeqName : PEvalNames -> Name
  sem mapToSeqName = | names -> getName (names.otherFuncs) "mapToSeq"

  sem noSymbolName : PEvalNames -> Name
  sem noSymbolName = | names -> getName (names.consNames) "_noSymbol"

  sem stringToSidName : PEvalNames -> Name
  sem stringToSidName = | names -> getName (names.otherFuncs) "stringToSid"

  sem mexprStringName : PEvalNames -> Name
  sem mexprStringName = | names -> getName (names.otherFuncs) "toString" 

  sem patIntName : PEvalNames -> Name
  sem patIntName = | names -> getName (names.consNames) "IntPat_PatInt" 

  sem patNamedName : PEvalNames -> Name
  sem patNamedName = | names -> getName (names.consNames) "NamedPat_PatNamed"

  sem pNameName: PEvalNames -> Name
  sem pNameName = | names -> getName (names.consNames) "PName"

  sem pWildcardName: PEvalNames -> Name
  sem pWildcardName = | names -> getName (names.consNames) "PWildcard"

  -- Return a string representation of the constant along with whether
  -- it takes an argument when constructed
  sem getConstString : Const -> String
  sem getConstString =
  | CInt _ -> "int"
  | CFloat _ -> "float"
  | CBool _ -> "bool"
  | CChar _ -> "char"
  | CSymb _ -> "symb"
  | t -> getConstStringCode 0 t

  sem getBuiltinName : String -> PEvalNames -> Name
  sem getBuiltinName str = | names ->
  match mapLookup str builtinsMapping with Some astStr then
    getName (names.builtinsNames) astStr
  else error (join ["Could not find ", str, " in builtin-mapping"])

  sem getBuiltinNameFromConst : Const -> PEvalNames -> Name
  sem getBuiltinNameFromConst val = | names ->
    let str = getConstString val in
    getBuiltinName str names
end
