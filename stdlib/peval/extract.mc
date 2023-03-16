
-- Try to reuse accelerate/extract.mc as much as possible
-- Difference here is that the 'extracted' nodes must be put together 


include "pmexpr/extract.mc"
include "peval/ast.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "mexpr/extract.mc"
include "mexpr/lamlift.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"


lang PEvalExtract = PMExprExtractAccelerate + PEvalAst 

  -- pmexpr/extract.mc 
  -- Very similar funcitons to pmexpr's extract.


  type PEvalData = AccelerateData 

  type AddIdentifierPEvalEnv = AddIdentifierAccelerateEnv

  sem addIdentifierToPEvalTerms =
  | t -> 
    let env = {
      functions = mapEmpty nameCmp,
      programIdentifiers = setEmpty cmpSID
    } in
    let env = collectProgramIdentifiers env t in
    match addIdentifierToPEvalTermsH env t with (env, t) in
    let env : AddIdentifierPEvalEnv = env in
    (env.functions, t)

  sem addIdentifierToPEvalTermsH (env : AddIdentifierPEvalEnv) =
  | TmPEval t -> replaceTermWithLet env {e=t.e, info = t.info, ty = tyTm t.e}
  | t -> smapAccumL_Expr_Expr addIdentifierToPEvalTermsH env t

end

lang TestLang =
   PEvalExtract + MExprEq + MExprSym + MExprTypeCheck + MExprPrettyPrint +
   MExprLambdaLift
end

mexpr

-- The below tests are very essentially identical to the ones in stdlid/pmexpr/extract.mc
-- But adapted to use 'peval' instead


use TestLang in

let preprocess = lam t.
  typeCheck (symbolize t)
in

let extractPeval = lam t.
  match addIdentifierToPEvalTerms t with (pevaled, t) in
  let ids = mapMap (lam. ()) pevaled in
  let t = liftLambdas t in
  (pevaled, extractAccelerateTerms ids t)
in

let noPevalCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  app_ (var_ "f") (int_ 2)
]) in
match extractPeval noPevalCalls with (m, ast) in
utest mapSize m with 0 in
utest ast with int_ 0 using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  peval_ (app_ (var_ "h") (int_ 2))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "h") (int_ 2))),
  int_ 0
]) in
match extractPeval t with (m, ast) in

utest mapSize m with 1 in
utest ast with extracted using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (app_ (var_ "f") (var_ "x")) (int_ 2))),
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  peval_ (app_ (var_ "g") (int_ 4))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (app_ (var_ "f") (var_ "x")) (int_ 2))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 4))),
  int_ 0
]) in
match extractPeval t with (m, ast) in
utest mapSize m with 1 in
utest ast with extracted using eqExpr in

let multipleCallsToSame = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (bindall_ [
    ulet_ "y" (addi_ (var_ "x") (int_ 2)),
    peval_ (app_ (var_ "f") (var_ "y"))
  ])),
  ulet_ "h" (ulam_ "x" (peval_ (app_ (var_ "f") (var_ "x")))),
  addi_
    (app_ (var_ "g") (int_ 1))
    (app_ (var_ "h") (int_ 3))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "t" (ulam_ "y" (ulam_ "" (app_ (var_ "f") (var_ "y")))),
  ulet_ "t" (ulam_ "x" (ulam_ "" (app_ (var_ "f") (var_ "x")))),
  int_ 0
]) in
match extractPeval multipleCallsToSame with (m, ast) in
utest mapSize m with 2 in
utest ast with extracted using eqExpr in

let distinctCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  addi_
    (peval_ (app_ (var_ "f") (int_ 1)))
    (peval_ (app_ (var_ "g") (int_ 0)))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "f") (int_ 1))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 0))),
  int_ 0
]) in
match extractPeval distinctCalls with (m, ast) in
utest mapSize m with 2 in
utest ast with extracted using eqExpr in

let distinctCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "h" (peval_ (app_ (var_ "g") (int_ 1))),
  ulet_ "z" (ulam_ "x" (app_ (var_ "f") (var_ "x"))),
  (peval_ (app_ (var_ "z") (int_ 1)))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 1))),
  ulet_ "z" (ulam_ "x" (app_ (var_ "f") (var_ "x"))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "z") (int_ 1))),
  int_ 0
]) in
match extractPeval distinctCalls with (m, ast) in
utest ast with extracted using eqExpr in

let inRecursiveBinding = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ureclets_ [
    ("g", ulam_ "x" (app_ (var_ "f") (addi_ (var_ "x") (int_ 1)))),
    ("h", ulam_ "x" (peval_ (app_ (var_ "g") (var_ "x"))))],
  app_ (var_ "h") (int_ 3)
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ureclets_ [
    ("g", ulam_ "x" (app_ (var_ "f") (addi_ (var_ "x") (int_ 1)))),
    ("t", ulam_ "x" (ulam_ "" (app_ (var_ "g") (var_ "x"))))],
  int_ 0
]) in
match extractPeval inRecursiveBinding with (m, ast) in
utest mapSize m with 1 in
utest ast with extracted using eqExpr in

let partialCalls = preprocess (bindall_ [
  ulet_ "g" (ulam_ "y" (ulam_ "x" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "h" (peval_ (app_ (var_ "g") (int_ 1)))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "g" (ulam_ "y" (ulam_ "x" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 1))),
  int_ 0
]) in
match extractPeval partialCalls with (m, ast) in
utest ast with extracted using eqExpr in

()

