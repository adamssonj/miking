include "common.mc"
include "string.mc"
include "option.mc"

mexpr

let foo = lam x.
  match x with Some 3 then 3 else 5 in

let r = peval (foo (Some 4)) in

printLn (int2string r)
