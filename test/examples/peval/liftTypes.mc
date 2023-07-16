include "common.mc"
include "string.mc"

mexpr

let foo = lam x:Char. specialize x in
let char = foo 'g' in

let foo = lam x:[Int]. specialize x in
let seq = foo [1,2,3] in

let foo = lam x:{a:Int, b:Float, c:(Int -> Int)}. specialize x in
let rec = foo {a=3, b= 5.0, c= lam x. (addi 1 x)} in

printLn "rec"
printLn (int2string (rec.a));
printLn (float2string (rec.b))

printLn "seq";
printLn (int2string (head seq));

printLn "char";
printLn ([char])
