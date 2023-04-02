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
include "mexpr/boot-parser.mc"


lang PEvalCompile = PEvalAst + MExprPEval + ClosAst + MExprAst
                    + PEvalInclude + PEvalLiftMExpr

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
  | t -> mapInsert name t lib
--  | TmLam t & lm -> mapInsert name lm lib
--  | _ -> lib

  sem pevalPass : PEvalNames -> Map Name Expr -> Map Name Name ->
                  Expr -> (Map Name Name, Expr)
  sem pevalPass pnames lib idMap =
  | TmLet ({ident=id, body=body, inexpr=inexpr, ty=ty, info=info} & t) ->
    match pevalPass pnames lib idMap body with (idMap, b) in
    let lib = insertToLib lib id b in
    match pevalPass pnames lib idMap inexpr with (idMap, inx) in
    (idMap, TmLet {t with body=b, inexpr=inx})
  | TmRecLets ({bindings=bindings, inexpr=inexpr, ty=ty, info=info} & t) ->
    let binds = mapAccumL (lam idMap. lam rl:RecLetBinding.
        match pevalPass pnames lib idMap rl.body with (idMap, b) in
        let recl = {rl with body = b} in
        (idMap, recl)) idMap bindings in

    match binds with (idMap, bindings) in
    let lib = foldl (lam lib. lam rl.
                    insertToLib lib rl.ident rl.body) lib bindings in
    match pevalPass pnames lib idMap inexpr with (idMap, inx) in
    (idMap, TmRecLets {t with inexpr=inx, bindings=bindings})
  | TmPEval {e=e, info=info} & pe ->
    let args = initArgs lib idMap in
    match liftExpr pnames args e with (args, pevalArg) in
    match getLiftedEnv pnames args [] e with (args, liftedEnv) in
    let lhs = nvar_ (pevalName pnames) in
    let f = appf2_ lhs liftedEnv pevalArg in
    let p = nvar_ (mexprStringName pnames) in
    let ff = app_ p f in
    let fff = print_ ff in
    (args.idMapping, semi_ fff never_)
  | t -> smapAccumL_Expr_Expr (pevalPass pnames lib) idMap t

  sem compilePEval =
  | origAst ->
    -- TODO(adamssonj, 2023-03-22): For now just always include
    match includePEval origAst with (ast, pevalNames) in
    match includeConstructors ast with ast in
    -- Find the names of the functions and constructors needed later
    let names = createNames ast pevalNames in
    match pevalPass names (mapEmpty nameCmp) (mapEmpty nameCmp) ast with (idMapping, ast) in
    let symDefs = bindall_ (map (lam n:Name. nulet_ n (gensym_ uunit_))
                (mapValues idMapping)) in
    let ast = bindall_ [
        symDefs,
        ast] in
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

let distinctCalls = preprocess (bindall_ [
  ulet_ "bar" (ulam_ "x" (ulam_ "y" (subi_ (var_ "x") (var_ "y")))),
--  ulet_ "foo" (ulam_ "x" (ulam_ "y" (addi_ (appf2_ (var_ "bar") (var_ "x") (var_ "y")) 
--    (var_ "y")))),
  peval_ (app_ (var_ "bar") (int_ 1))
]) in


let distinctCalls = preprocess (bindall_ [
  ulet_ "bar" (ulam_ "x" (ulam_ "y" (subi_ (var_ "x") (var_ "y")))),
--  ulet_ "foo" (ulam_ "x" (ulam_ "y" (addi_ (appf2_ (var_ "bar") (var_ "x") (var_ "y"))
--    (var_ "y")))),
  peval_ (app_ (var_ "bar") (int_ 1))
]) in


let distinctCalls = preprocess (bindall_ [
  ulet_ "foo" (ulam_ "x" (ulam_ "y" (subi_ (var_ "x") (var_ "y")))),
  ulet_ "bar" (app_ (var_ "foo") (int_ 3)),
  ulet_ "bars" (peval_ (var_ "bar"))
]) in

match compilePEval distinctCalls with ast in

let ast = typeAnnot ast in

()
