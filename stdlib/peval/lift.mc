-- Include here all the lifting that is now performed inside compile.mc
-- Not sure yet whether to include the name handling
-- That should probably go in a different file, or utils?
--
--
-- Should also make sure that every lift works as expected by having at least one test per
-- constructor here
--

include "peval/extract.mc"
include "peval/ast.mc"
include "peval/utils.mc"

include "mexpr/ast-builder.mc"
include "mexpr/eval.mc"

include "list.mc"
include "string.mc"
include "stringid.mc"
include "error.mc"


lang PEvalLift = PEvalAst + PEvalUtils + MExprAst + ClosAst

  -- liftExpr should produce an Expr s.t. when evaluated produces its original input argument
  -- In that sense liftExpr can be considered an inverse of 'eval'
  sem liftExpr : PEvalNames -> Expr -> Expr
  sem liftExpr names = | t -> printLn "Don't know how to lift this yet!"; t

  sem createConApp : PEvalNames ->  (PEvalNames -> Name)
                    -> [(String, Expr)] -> Type
                    -> Expr -- TmConApp
  sem createConApp names getName bindings =
  | typ -> --let ltype = liftType names typ in
           let rec = urecord_ bindings in
           nconapp_ (getName names) rec

  sem createConAppInfo names getName bindings typ =
  | info -> let bindings = cons ("info", liftInfo names info) bindings in
            createConApp names getName bindings typ


  sem createConAppExpr names getName bindings typ =
  | info -> let bindings = cons ("ty", liftType names typ) bindings in
            createConAppInfo names getName bindings typ info

  sem liftType : PEvalNames -> Type -> Expr
  sem liftType names =
  | t -> match tyConInfo t with (info, getName) in
    createConAppInfo names getName [] tyunknown_ info

  sem tyConInfo : Type -> (Info, (PEvalNames -> Name))
  sem tyConInfo =
  | TyUnknown {info = info} -> (info, tyUnknownName) 
  -- | TyArrow {info = info, from = from, to = to} -> (info, tyArrowName)
  | t -> printLn "Don't know how to lift this type"; (NoInfo(), tyUnknownName)

  sem liftName : PEvalNames -> (String, Symbol) -> Expr
  sem liftName names = | tup ->
    let nosym = nvar_ (noSymbolName names) in
    utuple_ [str_ tup.0, nosym]

  sem liftInfo : PEvalNames -> Info -> Expr
  sem liftInfo names =
  | _ -> createConApp names noInfoName [] tyunknown_
    
  -- Parse tuple to expr
  sem envItemToTuple : PEvalNames -> (Name, Expr) -> Expr
  sem envItemToTuple names = | tup ->
    let name = liftName names tup.0 in
    let expr = liftExpr names tup.1 in
    utuple_ [name, expr]
end

lang PEvalLiftApp = PEvalLift + AppAst

  sem liftExpr names =
  | TmApp {lhs = lhs, rhs = rhs, info = info, ty=typ} ->
    let lhs = liftExpr names lhs in -- Should be either TmVar or TmConst
    let rhs = liftExpr names rhs in
    let bindings = [("lhs", lhs), ("rhs", rhs)] in
    createConAppExpr names tmAppName bindings typ info

  sem tyConInfo =
  | TyApp {info = info, lhs = lhs, rhs=rhs} -> (info, tyAppName)
end

lang PEvalLiftVar = PEvalLift + VarAst

  sem liftViaType : PEvalNames -> Map Name Expr -> Name -> Type -> Option Expr
  sem liftViaType names lib varName =
  | TyInt {info = info} & typ ->
    let lv = TmVar {ident = varName, ty=typ, info = NoInfo (), frozen = false} in
    let bindings = [("val", lv)] in
    let const = createConApp names (getBuiltinName "int") bindings typ in
    let bindings = [("val", const)] in
    Some (createConAppExpr names tmConstName bindings typ info)
  | TySeq {info = info, ty = ty} ->
    let sq = TmVar {ident = varName, ty=ty, info = NoInfo (),
                    frozen = false} in
    match liftViaType names lib (nameNoSym "x") ty with Some t then
        let convert = (lam_ "x" ty t) in
        let tms = map_ convert sq in
        let bindings = [("tms", tms)] in
        Some (createConAppExpr names tmSeqName bindings ty info)
    else None () -- We don't know how to lift element types

  -- | TyRec t ->
  | ty ->
    match mapLookup varName lib with Some t then
        Some (liftExpr names t)
    else
       None () -- We don't know how to lift this type and don't have its def.

  sem liftExpr names =
  | TmVar {ident = id, ty = typ, info = info, frozen = frozen} ->
    let bindings = [("ident", liftName names id),
                    ("frozen", bool_ frozen)] in
    createConAppExpr names tmVarName bindings typ info

  sem tyConInfo =
  | TyVar {info = info, ident = id, level = lv} -> (info, tyVarName)

end

lang PEvalLiftRecord = PEvalLift + RecordAst

  sem liftExpr names =
  | TmRecord {bindings = binds, info=info, ty = typ} ->
    let binSeq = mapToSeq binds in
    let exprs =  seq_ (map (lam x. utuple_ [int_ x.0, liftExpr names x.1])
                    binSeq) in
    let lhs = nvar_ (mapFromSeqName names) in
    -- cmpSID = subi
    let rhs = (uconst_ (CSubi ())) in
    let bin = appf2_ lhs rhs exprs in
--    let lhs = app_ lhs rhs in
--    let bin = app_ lhs exprs in
    let bindings = [("bindings", bin)] in
    createConAppExpr names tmRecName bindings typ info

    
end

lang PEvalLiftSeq = PEvalLift
  sem liftExpr names =
  | TmSeq {tms = exprs, ty = typ, info = info} ->
    let exprs = map (liftExpr names) exprs in
    let bindings = [("tms", seq_ exprs)] in
    createConAppExpr names tmSeqName bindings typ info

end

lang PEvalLiftConst = PEvalLift + ConstAst

  sem buildConstBindings : Const -> [(String, Expr)]
  sem buildConstBindings =
  | CInt {val = v} -> [("val", int_ v)]
  | CFloat {val = v} -> [("val", float_ v)]
  | CBool {val = v} -> [("val", bool_ v)]
  | CChar {val = v} -> [("val", char_ v)]
  | CSymb {val = v} -> [("val", symb_ v)]
  | t -> []

  sem liftExpr names =
  | TmConst {val = const, ty = typ, info = info} & t ->
    let bindings = buildConstBindings const in
    -- Build "Const"
    let const = createConApp names (getBuiltinNameFromConst const) bindings typ in
    let bindings = [("val", const)] in
    createConAppExpr names tmConstName bindings typ info

  sem tyConInfo =
  | TyInt {info = info} -> (info, tyIntName)
  | TyBool {info = info} -> (info, tyBoolName)
  | TyFloat {info = info} -> (info, tyFloatName)
  | TyChar {info = info} -> (info, tyCharName)

end


lang PEvalLiftPEval = PEvalLift + VarAst + PEvalAst

  sem buildClosureEnv (lib : Map Name Expr) (env : EvalEnv) =
  | TmVar t -> match mapLookup t.ident lib with Some b then
             evalEnvInsert t.ident b env else env
  | t -> sfold_Expr_Expr (buildClosureEnv lib) env t

  sem expandPEval (names : PEvalNames) (lib : Map Name Expr) =
  | TmPEval e & pe ->
    liftExpr names pe
  | t -> smap_Expr_Expr (expandPEval names lib) t

  sem liftConsList : PEvalNames -> List Expr -> Expr
  sem liftConsList names =
  | Cons (a, b) -> let bindings = [("0", a), ("1", liftConsList names b)] in
        createConApp names listConsName bindings tyunknown_
  | Nil _ -> createConApp names listNilName [] tyunknown_


  sem liftExpr names =
  | TmPEval {e = expr, info = info} ->
    error "Nested peval"
end


lang PEvalLiftLam = PEvalLift + LamAst
  sem liftExpr names =
  | TmLam {ident=id, body = body, ty = typ, info = info} ->
        let body = liftExpr names body in
        let bindings = [("ident", liftName names id), ("body", body)] in
        createConAppExpr names tmLamName bindings typ info
end

lang PEvalLiftMExpr =
    PEvalLiftApp + PEvalLiftVar + PEvalLiftRecord +
    PEvalLiftSeq + PEvalLiftConst + PEvalLiftLam + PEvalLiftPEval
end


lang TestLang = PEvalLiftMExpr + MExprPrettyPrint + MExprEval + MExprTypeCheck + MExprSym
                + MExprEq + MExprEval
end

lang SetupLang = PEvalInclude + PEvalUtils end

let _setup =
  use SetupLang in
  let ast = ulet_ "t" (int_ 3) in
  match includePEval ast with (ast, pevalNames) in
  match includeConstructors ast with ast in
  -- Find the names of the functions and constructors needed later
  let names = createNames ast pevalNames in
  names

mexpr
-- Possible idea:
--  Define expr:
--      1. Lift expr
--      2. Pprint lifted expr, and then interpret it. Is this = to interpreting expr directly?
use TestLang in
--
---- Dummy AST s.t. constructors and funcs can be included and used in lifting
let names = _setup in
--
--let lib : Map Name Expr = (mapEmpty nameCmp) in
--
------------ TmApp -----------------
--
------------ TmVar -----------------
--
--let expr = var_ "f" in
--let lift = liftExpr names expr in
--
--
------------ TmRecord -----------------

let x = nameSym "x" in 


let expr = urecord_ [("abc", int_ 3), ("def", int_ 4)] in
let lift = liftExpr names expr in

printLn (mexprToString lift);

------------ TmSeq -----------------
--
------------ TmConst -----------------
--
------------ TmLam -----------------
--
()
