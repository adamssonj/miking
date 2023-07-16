include "common.mc"
include "string.mc"
include "map.mc"
include "name.mc"

mexpr

    let foo = lam x. lam y.
        addi x y in
    let bar = foo in

let f = lam. 

    let bars = peval bar in 

    let res = bars 15 13 in

    printLn (int2string res) in

f ()


-- Problem:
-- liftExpr TmVar ==> '(TmVar)
-- liftViaType (->) ==>  lookUpInLib
--
--
--
-- This case we consider an edge case essentially.
-- If it is something that happens often, it might be worth making a special case for. 
-- But what we have now works good enough basically
