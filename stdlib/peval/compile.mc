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
include "mexpr/lamlift.mc"
include "mexpr/type-annot.mc"
include "mexpr/boot-parser.mc"
include "pmexpr/extract.mc"


lang PEvalCompile = PEvalAst + MExprPEval + ClosAst + MExprAst
                    + PEvalInclude + PEvalLiftMExpr --+ PMExprExtractAccelerate
                    + MExprLambdaLift + PEvalExtract

  -- Creates a library of the expressions that the element of specialization depends on
  sem createLib (lib : Map Name Expr) (pevalIds : Map Name PEvalData) =
  | TmLet t ->
    let lib2 = match mapLookup t.ident pevalIds with Some _ then lib
               else mapInsert t.ident t.body lib in
    createLib lib2 pevalIds t.inexpr
  | TmRecLets t ->
    foldl (lam lib. lam rl. mapInsert rl.ident rl.body lib) lib (t.bindings)
  | t -> lib

  -- Only inserts definition that can be of use when lifting.
  -- I.e. only co-data (TyArrow) or anything containing co-data
  -- TODO: Look at storing things that contain co-data
  sem insertToLib : PEvalArgs -> Name -> Expr -> PEvalArgs
  sem insertToLib args name = | t -> switch tyTm t
    case TyArrow _ then updateLib args (mapInsert name t args.lib)
    case _ then args
  end

  -- All reclet bindings have rhs that are lambdas
  sem insertRecLetBindings : PEvalArgs -> [RecLetBinding] -> PEvalArgs
  sem insertRecLetBindings args =
  | ts ->
    let names = map (lam x. x.ident) ts in
    let rll = foldl (lam lib. lam bind.
                mapInsert bind.ident (names, bind) lib) args.rlMapping ts in
    updateRlMapping args rll

  sem pevalPass : PEvalNames -> PEvalArgs -> Map Name Name ->
                  Expr -> (Map Name Name, Expr)
  sem pevalPass pnames args idMap =
  | TmLet ({ident=id, body=body, inexpr=inexpr, ty=ty, info=info} & t) ->
    match pevalPass pnames args idMap body with (idMap, b) in
    let args = insertToLib args id b in
    match pevalPass pnames args idMap inexpr with (idMap, inx) in
    (idMap, TmLet {t with body=b, inexpr=inx})
  | TmRecLets ({bindings=bindings, inexpr=inexpr, ty=ty, info=info} & t) ->
    let binds = mapAccumL (lam idMap. lam rl:RecLetBinding.
        match pevalPass pnames args idMap rl.body with (idMap, b) in
        let recl = {rl with body = b} in
        (idMap, recl)) idMap bindings in
    match binds with (idMap, bindings) in
    let args = insertRecLetBindings args bindings in
    match pevalPass pnames args idMap inexpr with (idMap, inx) in
    (idMap, TmRecLets {t with inexpr=inx, bindings=bindings})
  | TmPEval {e=e, info=info} & pe ->
    let args = updateIds args idMap in
    match liftExpr pnames args e with (args, pevalArg) in
    match getLiftedEnv pnames args [] e with (args, liftedEnv) in
    let lhs = nvar_ (pevalName pnames) in
    -- temporary
    let f = appf2_ lhs liftedEnv pevalArg in
    let p = nvar_ (mexprStringName pnames) in
    let ff = app_ p f in
    let fff = print_ ff in
    (args.idMapping, semi_ fff never_)
  | t -> smapAccumL_Expr_Expr (pevalPass pnames args) idMap t


  sem hasPEvalTerm : Bool -> Expr -> Bool
  sem hasPEvalTerm acc =
  | TmPEval _ -> true
  | t -> or acc (sfold_Expr_Expr hasPEvalTerm acc t)

  sem compilePEval =
  | ast ->
    -- TODO(adamssonj, 2023-03-22): For now just always include, (should check pevalterm exist)
    if not (hasPEvalTerm false ast) then ast
    else
    match includePEval ast with (ast, pevalNames) in
    match includeConstructors ast with ast in
    -- Find the names of the functions and constructors needed later
    let names = createNames ast pevalNames in
    match pevalPass names (initArgs ()) (mapEmpty nameCmp) ast
      with (idMapping, ast) in
    let symDefs = bindall_ (map (lam n:Name. nulet_ n (gensym_ uunit_))
                (mapValues idMapping)) in
    let ast = bindall_ [
        symDefs,
        ast] in
--    printLn (mexprToString ast);
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


-- TyInt
let unknownTyInt = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" tyint_ (peval_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (int_ 4)),
    unit_
]) in

-- TyFloat
let unknownTyFloat = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" tyfloat_ (peval_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (float_ 4.0)),
    unit_
]) in

-- TyBool
let unknownTyBool = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" tybool_ (peval_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (bool_ false)),
    unit_
]) in

-- TyChar
let unknownTyChar = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" tychar_ (peval_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (char_ 'x')),
    unit_
]) in

-- TySeq
let intseq = tyseq_ tyint_ in
let distinctCalls = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" intseq (peval_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (seq_ [int_ 1, int_ 2])),
    unit_
]) in

-- TyRec
let t = tyrecord_ [("a", tyint_), ("b", tyint_)] in
let distinctCalls = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" t (peval_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (urecord_ [("a",int_ 1), ("b", int_ 1)]))
]) in

let recursiveThing = preprocess (bindall_ [
    (ureclets_
       [("odd",
         ulam_ "x"
           (if_ (eqi_ (var_ "x") (int_ 1))
              true_
              (if_ (lti_ (var_ "x") (int_ 1))
                 false_
                 (app_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))),

        ("even",
         ulam_ "x"
           (if_ (eqi_ (var_ "x") (int_ 0))
              true_
              (if_ (lti_ (var_ "x") (int_ 0))
                 false_
                 (app_ (var_ "odd") (subi_ (var_ "x") (int_ 1))))))]),
    ulet_ "ra" (peval_ (app_ (var_ "odd") (int_ 4)))]) in

let e = match_ (int_ 3) (pvar_ "wo") (int_ 5) (int_ 6) in
let e = bind_ (ulet_ "x" (int_ 3)) (addi_ (int_ 4) (var_ "x")) in
let distinctCalls = preprocess (bindall_ [
    ulet_ "k" (peval_ (e))
]) in

match compilePEval unknownTyChar with ast in

let ast = typeAnnot ast in

()
