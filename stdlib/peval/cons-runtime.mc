include "mexpr/ast.mc"
include "mexpr/eval.mc" -- tmClos
include "mexpr/info.mc"

let tmApp = use AppAst in
    lam x. TmApp x

let tmLam = use LamAst in
    lam x. TmLam x

let tmVar = use VarAst in
    lam x. TmVar x

let tmRec = use RecordAst in
    lam x. TmRecord x

let tmSeq = use SeqAst in
    lam x. TmSeq x

let tmClos = use ClosAst in
    lam x. TmClos x

let tmConst = use ConstAst in
    lam x. TmConst x

--TODO: Add every constructor needed here
-- Could be added like let tmVar = use VarAst in lam x. TmVar x

mexpr

(tmApp, tmLam, tmVar, tmRec, tmSeq, tmClos, tmConst)
