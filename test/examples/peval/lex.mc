include "parser/lexer.mc"
include "common.mc"
include "mexpr/info.mc"


mexpr
use Lexer in

let fastLex = 
  lam r. peval (nextToken r) in 


let lexplex = lam str.
  let start = initPos "file" in
  fastLex {pos=start, str=str} in


lexplex "--foo \n bar " 


