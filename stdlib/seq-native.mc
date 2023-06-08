-- MExpr-native alternative implementations of higher-order functions over
-- sequences. The below versions are slower than their intrisic counterparts.
include "error.mc"

let map = lam f. lam s.
  recursive let rec = lam s.
    match s with [] then []
    else match s with [a] then [f a]
    else match s with [a] ++ ss then cons (f a) (rec ss)
    else never
  in rec s

let iter = lam f. lam s.  map f s; ()

utest map (lam x. addi x 1) [3,4,8,9,20] with [4,5,9,10,21]
utest map (lam x. addi x 1) [] with []

let mapi = lam f. lam s.
  recursive let rec = lam i. lam s.
    match s with [] then []
    else match s with [a] then [f i a]
    else match s with [a] ++ ss then cons (f i a) (rec (addi i 1) ss)
    else never
  in rec 0 s

let iteri = lam f. lam s. mapi f s; ()

utest mapi (lam i. lam x. i) [3,4,8,9,20] with [0,1,2,3,4]
utest mapi (lam i. lam x. i) [] with []

let foldl = lam f. lam acc. lam s.
  recursive let rec = lam acc. lam s.
    match s with [] then acc
    else match s with [a] ++ ss then rec (f acc a) ss
    else never
  in rec acc s

utest foldl addi 0 [1,2,3,4,5] with 15
utest foldl addi 0 [] with 0
utest map (foldl addi 0) [[1,2,3], [], [1,3,5,7]] with [6, 0, 16]

let foldr = lam f. lam acc. lam s.
  recursive let rec = lam acc. lam s.
    match s with [] then acc
    else match s with [a] ++ ss then f a (rec acc ss)
    else never
  in rec acc s

utest foldr (lam x. lam acc. x) 0 [1,2] with 1
utest foldr (lam acc. lam x. x) 0 [] with 0
utest foldr cons [] [1,2,3] with [1,2,3]

let create = lam l. lam f.
  recursive let rec = lam i. lam acc.
    if geqi i 0 then rec (subi i 1) (cons (f i) acc)
    else acc
  in rec (subi l 1) []

utest create 3 (lam. 10) with [10,10,10]
utest create 8 (lam. 'a') with ['a','a','a','a','a','a','a','a']
utest create 4 (lam i. muli 2 i) with [0,2,4,6]
utest create 0 (lam i. i) with []

let length = lam s. foldl (lam acc. lam. addi acc 1) 0 s

utest length [1,2,3,4] with 4
utest length [] with 0

let get = lam seq. lam index.
  recursive let rec = lam s. lam i.
    if eqi i 0 then
      match s with [a] ++ _ then a else
      error "Index out of bounds"
    else match s with [_] ++ ss then
      rec ss (subi i 1)
      else error "Index out of bounds"
  in
  if geqi index 0 then rec seq index
  else error "Negative index"

utest get [1,2,3,4] 0 with 1
utest get [1,2,3,4,5] 4 with 5
utest get [1] 0 with 1

let reverse = lam seq.
  foldl (lam acc. lam elem. cons elem acc) [] seq

utest reverse [1,2,3] with [3,2,1]
utest reverse (create 0 (lam i. i)) with []

let null = lam seq.
  match seq with [] then true else false

utest null [] with true
utest null [1,2,3] with false

let subsequence = lam seq. lam start. lam len.
  recursive let rec = lam acc. lam s. lam i. lam len.
    if lti i start then
      match s with [x] ++ xs then rec acc xs (addi i 1) len
      else acc
    else
      if gti len 0 then
        match s with [] then acc
        else match s with [x] then cons x acc
        else match s with [x] ++ xs then rec (cons x acc) xs (addi i 1) (subi len 1)
        else never
      else acc
  in if null seq then seq
     else reverse (rec [] seq 0 len)

utest subsequence [1,2,3] 0 3 with [1,2,3]
utest subsequence (create 0 (lam i. i)) 2 5 with []
utest subsequence [0,1,2,3,4,5] 2 2 with [2,3]

let splitAt = lam seq. lam i.
  recursive let rec = lam lhs. lam rhs. lam index.
    if eqi index 0 then (reverse lhs, rhs)
    else match rhs with [x] ++ xs then rec (cons x lhs) xs (subi index 1)
    else match rhs with [x] then rec (cons x lhs) [] (subi index 1)
    else match rhs with [] then error "Invalid index"
    else never
  in
    if geqi i 0 then rec [] seq i
    else error "Invalid index"

utest splitAt (create 0 (lam i. i)) 0 with ([], [])
utest splitAt [1] 0 with ([], [1])
utest splitAt [1] 1 with ([1], [])
utest splitAt [1,2,3,4] 2 with ([1,2], [3,4])
utest (splitAt "heja" 3).0 with "hej"

let tail = lam seq.
  match seq with ([]) then []
  else match seq with [_] ++ xs then xs
  else never

utest tail [1,2,3] with [2,3]
utest tail [1] with []
utest tail (create 0 (lam i. i)) with []


let head = lam seq.
  match seq with [x] ++ _ then x
  else error "Empty list"

utest head [1,2,3] with 1
utest head [1] with 1
