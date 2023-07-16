include "common.mc"
include "string.mc"

mexpr

let foo : Int -> Int -> Int = lam x. lam y.
    addi x y in

-- foo is evaluated to a closure probably
-- and 'bar' to a closure with 'x' in the env bound to 1
let bar = foo 1 in

let bars : Int -> Int = peval bar in 

-- Must build the 'env' with that type
-- let bars : Int -> Int = pevalActual (TmClos {env = Lazy [(Name, Expr)], body = TmVar 'bar')

let res : Int = bars 15 in

--()
printLn (int2string res)


-- Right now the peval keyword just creates a closure around the argument
-- When evaluating the peval term it just evaluates the expression ('bar') in this case
