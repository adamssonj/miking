include "peval/include.mc" 
include "peval/ast.mc"

include "mexpr/utils.mc"
include "mexpr/pprint.mc"
include "mexpr/extract.mc"
include "mexpr/ast.mc"

include "set.mc"


lang PEvalUtils = PEvalAst + PEvalInclude + MExprPrettyPrint + MExprExtract + LamAst 

  type PEvalNames = {
    pevalNames : [Name],
    consNames : [Name],
    builtinsNames : [Name],
    tyConsNames : [Name],
    otherFuncs : [Name],
    nameMapPH : Name -- Holds the reference to the placeholder where a nameMap will
                     -- be inserted. Used later on to create a pprintEnv
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

  sem findNames : Expr -> [String] -> [Name]
  sem findNames ast = | includes ->
  let names = filterOption (findNamesOfStrings includes ast) in
  if eqi (length includes) (length names) then
      names
  else 
    let incs = setOfSeq cmpString includes in
    let nms = setOfSeq cmpString (map (lam x. x.0) names) in
    let diff = setSubtract incs nms in
    (map (lam str. printLn str; str) (setToSeq diff));
    error "A necessary include could not be found in the AST"

  sem createNames : Expr -> [Name] -> Name -> PEvalNames
  sem createNames ast pevalNames =
  | nameMapName ->
  let consNames = findNames ast includeConsNames in
  let builtinsNames = findNames ast includeBuiltins in
  let tyConsNames = findNames ast includeTyConsNames in
  let otherFuncs = findNames ast otherFuncs in
  {pevalNames = pevalNames, consNames = consNames,
   builtinsNames = builtinsNames, tyConsNames = tyConsNames,
   otherFuncs=otherFuncs, nameMapPH = nameMapName}

  sem getName : [Name] -> String -> Option Name
  sem getName names =
  | str -> find (lam x. eqString str x.0) names

  sem pevalName : PEvalNames -> Name
  sem pevalName = | names -> match getName (names.pevalNames) "pevalWithEnv" with Some t then t
                             else error "semantic function peval not found"

  sem jitName : PEvalNames -> Name
  sem jitName = | names -> match getName (names.otherFuncs) "jitCompile" with Some t then t
                             else error "JIT compile not found"

  sem nameCmpName : PEvalNames -> Name
  sem nameCmpName = | names -> match getName (names.otherFuncs) "nameCmp" with Some t then t
                             else error "nameCmp not found"

  sem tmClosName : PEvalNames -> Name
  sem tmClosName = | names -> match getName (names.consNames) "ClosAst_TmClos"
                              with Some t then t else error "TmClos not found"

  sem tmAppName : PEvalNames -> Name
  sem tmAppName = | names -> match getName (names.consNames) "AppAst_TmApp" with Some t then t
                             else error "TmApp not found"

  sem tmLamName : PEvalNames -> Name
  sem tmLamName = | names -> match getName (names.consNames) "LamAst_TmLam" with Some t then t
                             else error "TmLam not found"

  sem tmVarName : PEvalNames -> Name
  sem tmVarName = | names -> match getName (names.consNames) "VarAst_TmVar" with Some t then t
                             else error "TmVar not found"

  sem tmRecName : PEvalNames -> Name
  sem tmRecName = | names -> match getName (names.consNames) "RecordAst_TmRecord" with
                             Some t then t else error "TmRecord not found"

  sem tmSeqName : PEvalNames -> Name
  sem tmSeqName = | names -> match getName (names.consNames) "SeqAst_TmSeq" with
                             Some t then t else error "TmSeq not found"

  sem tmConstName : PEvalNames -> Name
  sem tmConstName = | names -> match getName (names.consNames) "ConstAst_TmConst" with
                             Some t then t else error "TmConst not found"

  sem tmMatchName : PEvalNames -> Name
  sem tmMatchName = | names -> match getName (names.consNames) "MatchAst_TmMatch" with
                             Some t then t else error "TmMatch not found"

  sem tmLetName : PEvalNames -> Name
  sem tmLetName = | names -> match getName (names.consNames) "LetAst_TmLet" with
                             Some t then t else error "TmLet not found"

  sem listConsName : PEvalNames -> Name
  sem listConsName = | names -> match getName (names.consNames) "Cons" with
                             Some t then t else error "List Cons not found"

  sem listNilName : PEvalNames -> Name
  sem listNilName = | names -> match getName (names.consNames) "Nil" with
                             Some t then t else error "List Nil not found"

  sem infoName : PEvalNames -> Name
  sem infoName = | names -> match getName (names.consNames) "Info" with
                             Some t then t else error "Info constructor not found"

  sem noInfoName : PEvalNames -> Name
  sem noInfoName = | names -> match getName (names.consNames) "NoInfo" with
                             Some t then t else error "NoInfo constructor not found"

  sem tyAppName : PEvalNames -> Name
  sem tyAppName = | names -> match getName (names.tyConsNames) "AppTypeAst_TyApp" with
                             Some t then t else error "TyApp not found"

  sem tyVarName : PEvalNames -> Name
  sem tyVarName = | names -> match getName (names.tyConsNames) "VarTypeAst_TyVar" with
                             Some t then t else error "TyVar not found"

  sem tyIntName : PEvalNames -> Name
  sem tyIntName = | names -> match getName (names.tyConsNames) "IntTypeAst_TyInt" with
                             Some t then t else error "TyInt not found"
  sem tyBoolName : PEvalNames -> Name
  sem tyBoolName = | names -> match getName (names.tyConsNames) "BoolTypeAst_TyBool" with
                             Some t then t else error "TyBool not found"

  sem tyFloatName : PEvalNames -> Name
  sem tyFloatName = | names -> match getName (names.tyConsNames) "FloatTypeAst_TyFloat" with
                             Some t then t else error "TyFloat not found"

  sem tyCharName : PEvalNames -> Name
  sem tyCharName = | names -> match getName (names.tyConsNames) "CharTypeAst_TyChar" with
                             Some t then t else error "TyChar not found"

  sem tyUnknownName : PEvalNames -> Name
  sem tyUnknownName = | names -> match getName (names.tyConsNames) "UnknownTypeAst_TyUnknown"
                                 with Some t then t else error "TyUnknown not found"

  sem tyArrowName : PEvalNames -> Name
  sem tyArrowName = | names -> match getName (names.tyConsNames) "FunTypeAst_TyArrow"
                               with Some t then t else error "TyArrow not found"


  sem mapFromSeqName : PEvalNames -> Name
  sem mapFromSeqName = | names -> match getName (names.otherFuncs) "mapFromSeq"
                                  with Some t then t else error "MapFromSeq not found"

  sem mapToSeqName : PEvalNames -> Name
  sem mapToSeqName = | names -> match getName (names.otherFuncs) "mapToSeq"
                                with Some t then t else error "mapToSeq not found"

  sem noSymbolName : PEvalNames -> Name
  sem noSymbolName = | names -> match getName (names.consNames) "_noSymbol"
                                with Some t then t else error "_noSymbol not found"

  sem stringToSidName : PEvalNames -> Name
  sem stringToSidName = | names -> match getName (names.otherFuncs) "stringToSid"
                          with Some t then t else error "stringToSid not found"

  sem mexprStringName : PEvalNames -> Name
  sem mexprStringName = | names -> match getName (names.otherFuncs) "toString" 
                          with Some t then t else error "mexprToString not found"

  sem patIntName : PEvalNames -> Name
  sem patIntName = | names -> match getName (names.consNames) "IntPat_PatInt" 
                          with Some t then t else error "IntPat not found"

  sem patNamedName : PEvalNames -> Name
  sem patNamedName = | names -> match getName (names.consNames) "NamedPat_PatNamed"
                          with Some t then t else error "PatNamed not found"

  sem pNameName : PEvalNames -> Name
  sem pNameName = | names -> match getName (names.consNames) "PName"
                          with Some t then t else error "PName not found"

  sem pWildcardName : PEvalNames -> Name
  sem pWildcardName = | names -> match getName (names.consNames) "PWildcard"
                          with Some t then t else error "PWildcard not found"

  sem nameMapName : PEvalNames -> Name
  sem nameMapName = | names -> names.nameMapPH

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
    match find (lam x. eqString str x.0) builtinsMapping with Some astStr then
        match getName (names.builtinsNames) astStr.1 with Some t in
        t
    else error "Could not find a builtin name"

  sem getBuiltinNameFromConst : Const -> PEvalNames -> Name
  sem getBuiltinNameFromConst val = | names ->
    let str = getConstString val in
    getBuiltinName str names
end
