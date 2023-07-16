include "common.mc"
include "string.mc"

mexpr

--let foo = lam x. lam y:Int. (x 3 y) in

let foo = lam x. lam y. addi x y in

let bar = specialize (foo 3) in

let s = bar 3 in

printLn (int2string s)
