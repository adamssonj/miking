include "peval/include.mc"
include "mexpr/utils.mc"


lang PEvalUtils = PEvalAst + PEvalInclude

  type PEvalNames = {
    pevalNames : [Name],
    consNames : [Name],
    builtinsNames : [Name]
  }

  sem findNames : Expr -> [String] -> [Name]
  sem findNames ast = | includes -> 
  let names = filterOption (findNamesOfStrings includes ast) in
  if eqi (length includes) (length names) then
    names
  else error "A necessary include could not be found in the AST"

  sem createNames : Expr -> [Name] -> PEvalNames
  sem createNames ast = 
  | pevalNames ->
  let consNames = findNames ast includeConsNames in
  let builtinsNames = findNames ast includeBuiltins in
  {pevalNames = pevalNames, consNames = consNames, 
   builtinsNames = builtinsNames}

  sem getName : [Name] -> String -> Option Name
  sem getName names = 
  | str -> find (lam x. eqString str x.0) names

  sem pevalName : PEvalNames -> Name
  sem pevalName = | names -> match getName (names.pevalNames) "peval" with Some t then t
                             else error "semantic function peval not found"

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

  sem getBuiltinName : Const -> PEvalNames -> Name
  sem getBuiltinName val = | names -> 
    let str = getConstString val in -- Find the string of the const
    -- str = 'addi' => Name.str == ArithIntAst_CAddi
    match find (lam x. eqString str x.0) builtinsMapping with Some astStr then
        match getName (names.builtinsNames) astStr.1 with Some t in
        t
    else error "Could not find a builtin name"
end
