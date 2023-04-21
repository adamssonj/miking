
include "peval/extract.mc"
include "peval/ast.mc"
include "peval/utils.mc"

include "mexpr/ast-builder.mc"
include "mexpr/eval.mc"
include "mexpr/cfa.mc" -- only for freevariables

include "mexpr/mexpr.mc"

include "list.mc"
include "seq.mc"
include "set.mc"
include "string.mc"
include "stringid.mc"
include "error.mc"
include "either.mc"

lang PEvalLift = PEvalAst + PEvalUtils + MExprAst + ClosAst

  type LiftResult = (PEvalArgs, Expr)

  -- liftExpr should produce an Expr s.t. when evaluated produces its original input argument
  -- In that sense liftExpr can be considered an inverse of 'eval'
  sem liftExpr : PEvalNames -> PEvalArgs -> Expr -> LiftResult
  sem liftExpr names args = | t -> printLn "Don't know how to lift this yet!"; (args, t)

  sem liftExprAccum : PEvalNames -> PEvalArgs -> [Expr] ->
                      (PEvalArgs, [Expr])
  sem liftExprAccum names args =
  | xs -> mapAccumL (lam args. lam e. liftExpr names args e) args xs

  sem createConApp : PEvalNames ->  (PEvalNames -> Name)
                    -> [(String, Expr)]
                    -> Expr -- TmConApp
  sem createConApp names getName =
  | bindings ->
    let rec = urecord_ bindings in
    nconapp_ (getName names) rec

  sem createConAppInfo names getName bindings =
  | info -> let bindings = cons ("info", liftInfo names info) bindings in
            createConApp names getName bindings

  sem createConAppExpr names getName bindings typ =
  | info -> let bindings = cons ("ty", liftType names typ) bindings in
            createConAppInfo names getName bindings info

  sem liftType : PEvalNames -> Type -> Expr
  sem liftType names =
  | t -> match tyConInfo t with (info, getName) in
    createConAppInfo names getName [] info

  sem tyConInfo : Type -> (Info, (PEvalNames -> Name))
  sem tyConInfo =
  | TyUnknown {info = info} -> (info, tyUnknownName) 
  | t -> printLn "Don't know how to lift this type"; (NoInfo(), tyUnknownName)

  sem liftName : PEvalArgs -> Name -> LiftResult
  sem liftName args = | name ->
    match mapLookup name args.idMapping with Some t then
      (args, utuple_ [str_ name.0, nvar_ t])
    else let idm = nameSym "idm" in
      let args = {args with idMapping = mapInsert name idm args.idMapping} in
      (args, utuple_ [str_ name.0, nvar_ idm])

  sem liftInfo : PEvalNames -> Info -> Expr
  sem liftInfo names =
  | _ -> createConApp names noInfoName []
    

  sem liftStringToSID : PEvalNames -> String -> Expr
  sem liftStringToSID names = | x ->
   app_ (nvar_ (stringToSidName names)) (str_ x)

end

lang PEvalLiftApp = PEvalLift + AppAst

  sem liftExpr names args =
  | TmApp {lhs = lhs, rhs = rhs, info = info, ty=typ} ->
    match liftExprAccum names args [lhs, rhs] with (args, [lhs, rhs]) in
    let bindings = [("lhs", lhs), ("rhs", rhs)] in
    (args, createConAppExpr names tmAppName bindings typ info)

  sem tyConInfo =
  | TyApp {info = info, lhs = lhs, rhs=rhs} -> (info, tyAppName)
end

lang PEvalLiftVar = PEvalLift + VarAst

  sem liftViaType : PEvalNames -> PEvalArgs -> Name -> Type -> Option LiftResult
  sem liftViaType names args varName =
  | t & (TyInt _ | TySeq _ | TyRecord _) ->
    match liftViaTypeH names varName t with Some t then Some (args, t)
    else None ()
  | ty ->
    match mapLookup varName args.lib with Some t then
      let args = updateClosing args false in
      Some (liftExpr names args t)
    else None ()

  -- NOTE(adamssonj, 2023-03-31): Can't do anything with e.g. [(a->b)] aon
  sem liftViaTypeH : PEvalNames -> Name -> Type -> Option Expr
  sem liftViaTypeH names varName =
  | TyInt {info = info} & typ ->
    let lv = TmVar {ident = varName, ty=typ, info = NoInfo (), frozen = false} in
    let bindings = [("val", lv)] in
    let const = createConApp names (getBuiltinName "int") bindings in
    let bindings = [("val", const)] in
    Some (createConAppExpr names tmConstName bindings typ info)
  | TySeq {info = info, ty = ty} & typ->
    let sq = TmVar {ident = varName, ty=typ, info = NoInfo (),
                    frozen = false} in
    -- TODO: Should not be unsymbolized "x"
    match liftViaTypeH names (nameNoSym "x") ty with Some t then
        let convert = (lam_ "x" ty t) in
        let tms = map_ convert sq in
        let bindings = [("tms", tms)] in
        Some (createConAppExpr names tmSeqName bindings ty info)
    else None () -- We don't know how to lift element types
  | TyRecord {info=info, fields=fields} & typ ->
    -- fields : Map SID Type
    let rec = TmVar {ident = varName, ty = typ, info = NoInfo (),
                    frozen = false} in

    let seqFields = mapToSeq fields in
    let patternList = map (lam x. let s = sidToString x.0 in
                        (s, pvar_ s)) seqFields in

    let pat = prec_ patternList in
    -- Create one lifted type per record entry
    -- Should probably do it only once per type, and map id -> typelift
    let seqFieldsWithLift = map (lam x. (x.0, x.1,
                 liftViaTypeH names (nameNoSym "x") x.1)) seqFields in

    -- If we cannot lift any of the present types
    if any (lam x. optionIsNone x.2) seqFieldsWithLift then None ()
    else

    let s = seq_ (map (lam x.
      let s = sidToString x.0 in
      match x.2 with Some t in
        let convert = (lam_ "x" x.1 t) in
        let liftedType = app_ convert (var_ s) in
        utuple_ [liftStringToSID names s, liftedType]) seqFieldsWithLift)
      in
    let thn = appf2_ (nvar_ (mapFromSeqName names)) (uconst_ (CSubi ())) s in
    let mbind = matchex_ rec pat thn in

    let bindings = [("bindings", mbind)] in
    Some (createConAppExpr names tmRecName bindings typ info)
  | t -> None ()


  sem liftExpr names args =
  | TmVar {ident = id, ty = typ, info = info, frozen = frozen} ->
    match liftName args id with (args, lIdent) in
    let bindings = [("ident", lIdent),
                    ("frozen", bool_ frozen)] in
    (args, createConAppExpr names tmVarName bindings typ info)

  sem tyConInfo =
  | TyVar {info = info, ident = id, level = lv} -> (info, tyVarName)

end

lang PEvalLiftRecord = PEvalLift + RecordAst

  sem liftExpr names args =
  | TmRecord {bindings = binds, info=info, ty = typ} ->
    match unzip (mapToSeq binds) with (ids, exprs) in
    match liftExprAccum names args exprs with (args, lExprs) in
    let binSeq = zip ids lExprs in
    let exprs =  seq_ (map (lam x. utuple_
      [liftStringToSID names (sidToString x.0) ,x.1]) binSeq) in
    let lhs = nvar_ (mapFromSeqName names) in
    -- cmpSID = subi
    let rhs = (uconst_ (CSubi ())) in
    let bin = appf2_ lhs rhs exprs in
    let bindings = [("bindings", bin)] in
    (args, createConAppExpr names tmRecName bindings typ info)
end

lang PEvalLiftSeq = PEvalLift
  sem liftExpr names args =
  | TmSeq {tms = exprs, ty = typ, info = info} ->
    match liftExprAccum names args exprs with (args, lExprs) in
    let bindings = [("tms", seq_ lExprs)] in
    (args, createConAppExpr names tmSeqName bindings typ info)
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

  sem liftExpr names args =
  | TmConst {val = const, ty = typ, info = info} & t ->
    let bindings = buildConstBindings const in
    -- Build "Const"
    let const = createConApp names (getBuiltinNameFromConst const) bindings in
    let bindings = [("val", const)] in
    (args, createConAppExpr names tmConstName bindings typ info)

  sem tyConInfo =
  | TyInt {info = info} -> (info, tyIntName)
  | TyBool {info = info} -> (info, tyBoolName)
  | TyFloat {info = info} -> (info, tyFloatName)
  | TyChar {info = info} -> (info, tyCharName)

end


lang PEvalLiftPEval = PEvalLift + VarAst + PEvalAst

  sem liftExpr names args =
  | TmPEval {e = expr, info = info} ->
    error "Nested peval"
end


lang PEvalLiftLam = PEvalLift + LamAst + MExprKCFA + PEvalLiftVar

  sem liftConsList : PEvalNames -> List Expr -> Expr
  sem liftConsList names =
  | Cons (a, b) -> let bindings = [("0", a), ("1", liftConsList names b)] in
        createConApp names listConsName bindings
  | Nil _ -> createConApp names listNilName []

  sem buildEnv : PEvalNames -> PEvalArgs -> Map Name Type -> LiftResult
  sem buildEnv names args =
  | fvs ->
    let fvs = mapToSeq fvs in -- [(Name, Type])
    match liftAllViaType names args fvs with (args, liftedEnvItems) in
    match eitherPartition liftedEnvItems with (fvs, liftedExprs) in
    -- For the fvs that we couldn't lift, there's a chance they're reclet binds
    match handleRecLet names args fvs with (args, liftedEnvItems) in
    let liftedExprs = concat liftedExprs (filterOption liftedEnvItems) in
    let lenv = liftConsList names (listFromSeq liftedExprs) in
    (args, lenv)


  sem handleRecLet : PEvalNames -> PEvalArgs -> [Name] ->
                     (PEvalArgs, [Option Expr])
  sem handleRecLet names args =
  | ns ->
    -- [([Name], RecLetBinding)]
    let binds = filterOption (map (lam name. mapLookup name args.rlMapping) ns) in
    let ns = join (map (lam bs:([Name], RecLetBinding). bs.0) binds) in
    let ns = setToSeq (setOfSeq nameCmp ns) in -- [Name] unique
    mapAccumL (lam acc. lam name.
        match mapLookup name args.rlMapping with Some t then
          -- Reclet bindings should have a rhs that is a TmLam
          -- I.e. liftViaType <=> liftExpr
          match t with (_, rlb) in
          match liftExpr names args rlb.body with (acc, liftedExpr) in
          match liftName acc name with (acc, liftedName) in
           (acc, Some (utuple_ [liftedName, liftedExpr]))
        else (acc, None ())) args ns

  sem liftAllViaType : PEvalNames -> PEvalArgs -> [(Name, Type)] ->
                      (PEvalArgs, [Either Name Expr])
  sem liftAllViaType names args =
  | ts -> mapAccumL (lam acc. lam t : (Name, Type).
    match liftViaType names acc t.0 t.1 with Some (acc, expr) then
      match liftName acc t.0 with (acc, liftedName) in
        (acc, Right (utuple_ [liftedName, expr]))
    else (acc, Left (t.0))) args ts

  sem getTypesOfVars : Set Name -> Map Name Type -> Expr -> Map Name Type
  sem getTypesOfVars freeVars varMapping =
  | TmVar {ident=id, ty=ty} ->
    if setMem id freeVars then mapInsert id ty varMapping
    else varMapping
  | ast -> sfold_Expr_Expr (getTypesOfVars freeVars) varMapping ast

  sem getLiftedEnv : PEvalNames -> PEvalArgs -> [Name] -> Expr -> LiftResult
  sem getLiftedEnv names args exclude =
  | expr ->
    -- From /mexpr/cfa.mc
    let fvs = freeVars (setEmpty nameCmp) expr in
    let fvs = setSubtract fvs (setOfSeq nameCmp exclude) in
    let typedFvs = getTypesOfVars fvs (mapEmpty nameCmp) expr in
    buildEnv names args typedFvs

  sem liftExpr names args =
  | TmLam {ident=id, body = body, ty = typ, info = info} ->
    if isClosing args then -- TmLam
      match liftExpr names args body with (args, lExpr) in
      match liftName args id with (args, lName) in
      let dummyType = liftType names tyunknown_ in
      let bindings = [("ident", lName), ("body", lExpr),
                      ("tyAnnot", dummyType), ("tyIdent", dummyType)] in
      (args, createConAppExpr names tmLamName bindings typ info)
    else -- Create closure
      let args = updateClosing args true in
      match liftExpr names args body with (args, lBody) in
      match getLiftedEnv names args [id] body with (args, liftedEnv) in
      match liftName args id with (args, liftedName) in
      let lazyLEnv = lam_ "t" tyunit_ liftedEnv in
      let bindings = [("ident", liftedName), ("body", lBody),
                      ("env", lazyLEnv)] in
      (args, createConAppInfo names tmClosName bindings info)
end


lang PEvalLiftMatch = PEvalLift + MatchAst

  sem liftPatName names args =
  | PName id -> match liftName args id with (args, lName) in
    let v = nconapp_ (pNameName names) lName in
    (args, v)
  | PWildcard _ -> let v = createConApp names pWildcardName [] in
    (args, v)

  sem liftPattern names args =
  | PatInt {val = v, info = info, ty=ty} ->
    let bindings = [("val", int_ v)] in
    (args, createConAppExpr names patIntName bindings ty info)
  | PatNamed {ident=ident, info=info, ty=ty} ->
    match liftPatName names args ident with (args, lPatName) in
    let bindings = [("ident", lPatName)] in
    (args, createConAppExpr names patNamedName bindings ty info)

  sem liftExpr names args =
  | TmMatch {target=target, pat=pat, thn=thn, els=els, ty=ty, info=info} ->
    match liftPattern names args pat with (args, lPat) in
    match liftExprAccum names args [target, thn, els]
      with (args, [lTarget, lThn, lEls]) in
    let bindings = [("target", lTarget), ("pat", lPat),
                    ("thn", lThn), ("els", lEls)] in
    (args, createConAppExpr names tmMatchName bindings ty info)
end


lang PEvalLiftLet = PEvalLift + LetAst


  sem liftExpr names args =
  | TmLet {ident=ident, body=body, inexpr=inexpr, ty=ty, info=info} ->
    match liftExprAccum names args [body, inexpr] with (args, [lBody, lInex]) in
    match liftName args ident with (args, lName) in
    let dummyType = liftType names tyunknown_ in
    let bindings = [("ident", lName), ("body", lBody), ("inexpr", lInex),
                  ("tyAnnot", dummyType), ("tyBody", dummyType)] in
    (args, createConAppExpr names tmLetName bindings ty info)

end

lang PEvalLiftMExpr =
    PEvalLiftApp + PEvalLiftVar + PEvalLiftRecord +
    PEvalLiftSeq + PEvalLiftConst + PEvalLiftLam + PEvalLiftPEval +
    PEvalLiftMatch + PEvalLiftLet

end


lang TestLang = PEvalLiftMExpr + MExprPrettyPrint + MExprEval + MExprSym
                + MExprEq
end

lang SetupLang = PEvalInclude + PEvalUtils end

let _setup =
  use SetupLang in
  let ast = ulet_ "t" (int_ 3) in
  match includePEval ast with (ast, pevalNames) in
  match includeConstructors ast with (ast, nameMapName) in
  -- Find the names of the functions and constructors needed later
  let names = createNames ast pevalNames nameMapName in
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
let args = initArgs () in


let _parse =
  parseMExprString
    { _defaultBootParserParseMExprStringArg () with allowFree = true }
in

let _eval = lam x.
  eval (evalCtxEmpty ()) x in

let _parseEval = lam x:String. 
  let x = _parse x in 
  _eval x in

--
------------ TmApp -----------------
--
let e = addi_ (int_ 1) (int_ 3) in

let k = liftExpr names args e in

--utest _eval e with evalStr st using eqExpr in

--
------------ TmVar -----------------
--

let e = var_ "t" in
let k = liftExpr names args e in


--
------------ TmRecord -----------------
let e = urecord_ [("a", int_ 3), ("b", int_ 4)] in
let k = liftExpr names args e in

------------ TmSeq -------------------

let e = seq_ (map int_ [1,2,3]) in
let k = liftExpr names args e in

------------ TmConst -----------------

let e = int_ 3 in
let k = liftExpr names args e in

--
------------ TmLam -----------------
----

let e = ulam_ "x" (addi_ (var_ "x") (int_ 3)) in
let k = liftExpr names args e in

--
------------ TmMatch -----------------
--

let e = match_ (int_ 3) (pvar_ "wo") (int_ 5) (int_ 6) in
let k = liftExpr names args e in

--
------------ TmLet -----------------
--

let e = bind_ (ulet_ "x" (int_ 3)) (addi_ (int_ 4) (var_ "x")) in
let k = liftExpr names args e in
printLn (mexprToString k.1);


()
