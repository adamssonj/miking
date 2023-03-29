include "peval/ast.mc"
include "peval/lift.mc"
include "peval/extract.mc"
include "peval/include.mc"

include "map.mc"
include "name.mc"
include "list.mc" -- listToSeq
include "seq.mc"
include "error.mc"
include "set.mc"

include "mexpr/ast.mc"
include "mexpr/type-annot.mc"
include "mexpr/cfa.mc" -- only for freevariables
include "mexpr/boot-parser.mc"


lang PEvalCompile = PEvalAst + MExprPEval + MExprKCFA +
                    ClosAst + MExprAst + PEvalInclude + PEvalLiftMExpr

  -- Creates a library of the expressions that the element of specialization depends on
  sem createLib (lib : Map Name Expr) (pevalIds : Map Name PEvalData) =
  | TmLet t ->
    let lib2 = match mapLookup t.ident pevalIds with Some _ then lib
               else mapInsert t.ident t.body lib in
    createLib lib2 pevalIds t.inexpr
  | TmRecLets t ->
    foldl (lam lib. lam rl. mapInsert rl.ident rl.body lib) lib (t.bindings)
  | t -> lib

  sem insertToLib : Map Name Expr -> Name -> Expr -> Map Name Expr
  sem insertToLib lib name =
  | TmLam t & lm -> mapInsert name lm lib
  | _ -> lib

  sem getTypesOfVars : Set Name -> Map Name Type -> Expr -> Map Name Type
  sem getTypesOfVars freeVars varMapping =
  | TmVar {ident=id, ty=ty} ->
    if setMem id freeVars then mapInsert id ty varMapping
    else varMapping
  | ast -> sfold_Expr_Expr (getTypesOfVars freeVars) varMapping ast

  sem gg : PEvalNames -> Map Name Expr ->
           List Expr -> Name -> Type -> List Expr
  sem gg names lib ls id =
  | typ ->
    match liftViaType names lib id typ with Some expr then
    listCons (utuple_ [liftName names id, expr]) ls
    else ls

  sem buildEnv : PEvalNames -> Map Name Expr
                -> Map Name Type -> List Expr
  sem buildEnv names lib =
  | fvs -> mapFoldWithKey (gg names lib) listEmpty fvs

  sem pevalPass : PEvalNames -> Map Name Expr -> Expr -> Expr
  sem pevalPass pnames lib =
  -- TODO recLet
  | TmLet ({ident=id, body=body, inexpr=inexpr, ty=ty, info=info} & t) ->
    let b = pevalPass pnames lib body in
    let lib = insertToLib lib id b in
    let inx = pevalPass pnames lib inexpr in
    TmLet {t with body=b,
                  inexpr=inx}
  | TmPEval {e=e, info=info} & pe ->
    let arg = liftExpr pnames e in
    -- From /mexpr/cfa.mc
    let fv = freeVars (setEmpty nameCmp) e in
    let mp = getTypesOfVars fv (mapEmpty nameCmp) e in
    let env = buildEnv pnames lib mp in
    let liftedEnv = liftConsList pnames env in
    let lhs = nvar_ (pevalName pnames) in
    let f = appf2_ lhs liftedEnv arg in
    let p = nvar_ (mexprStringName pnames) in
    let ff = app_ p f in
    let fff = print_ ff in
     semi_ fff never_
  | t -> smap_Expr_Expr (pevalPass pnames lib) t

  sem compilePEval =
  | origAst ->
    -- TODO(adamssonj, 2023-03-22): For now just always include
    match includePEval origAst with (ast, pevalNames) in
    match includeConstructors ast with ast in
    -- Find the names of the functions and constructors needed later
    let names = createNames ast pevalNames in
    let ast = pevalPass names (mapEmpty nameCmp) ast in
    --let ast = typeCheck ast in -- TODO: temporary fix
    printLn (mexprToString ast);
    ast
end


lang TestLang = PEvalCompile + MExprEq + MExprSym + MExprTypeCheck
                + MExprPrettyPrint + MExprTypeAnnot
end

mexpr
use TestLang in

let preprocess = lam t.
  typeCheck (symbolize t)
in


--let distinctCalls = preprocess (bindall_ [
--  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
--  peval_ (app_ (var_ "f") (int_ 1))
--]) in
--
--let distinctCalls = preprocess (bindall_ [
--  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
--  ulam_ "x" (bindall_ [
--    ulet_ "k" (addi_ (var_ "x") (var_ "x")),
--    ulet_ "q" (peval_ (var_ "k")),
--    var_ "k"
--    ])
--]) in
--
--let distinctCalls = preprocess (bindall_ [
--    ulet_ "f" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
--    ulet_ "p" (ulam_ "x" (peval_ (app_ (var_ "f") (var_ "x")))),
--    app_ (var_ "p") (int_ 4)
--]) in


let distinctCalls = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" tyint_ (peval_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (int_ 4)),
    unit_
]) in

let intseq = tyseq_ tyint_ in

let distinctCalls = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" intseq (peval_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (seq_ [int_ 1, int_ 2])),
    unit_
]) in

let t = tyrecord_ [("a", tyint_), ("b", tyfloat_)] in

let distinctCalls = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" t (peval_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (urecord_ [("a",int_ 1), ("b", float_ 1.0)]))
]) in

match compilePEval distinctCalls with ast in

let ast = typeAnnot ast in

()
