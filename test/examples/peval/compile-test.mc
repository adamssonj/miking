include "common.mc"
include "string.mc"
include "mexpr/ast.mc"
include "mexpr/pprint.mc"
include "name.mc"
include "map.mc"

mexpr

let bar = lam x1. lam y1.
    subi x1 y1 in

let foo = lam x. lam y.
    bar y x in

let ok = specialize foo in

let res = ok 13 15 in

printLn "hej";

printLn (int2string res)
