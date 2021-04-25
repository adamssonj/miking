open Ast
open Symbutils
open Ustring.Op
open Printf

(* Can be used when debugging symbol maps *)
let _symbmap = ref SymbMap.empty

(* Checks if a term _may_ have a side effect. It is conservative
   and returns only false if it is _sure_ to not have a side effect.
   The 'nmap' contains information (third element of the tuple) if
   a symbol may contain a side effect. *)
let rec tm_has_side_effect nmap acc = function
  | TmVar (_, _, s) -> (
      if acc then true
      else
        match SymbMap.find_opt s nmap with
        | Some (_, _, effect, _) ->
            effect
        | None ->
            false (* In case of lambda or pattern variables *) )
  | TmConst (_, c) ->
      if acc then true else const_has_side_effect c
  | TmRef (_, _) | TmTensor (_, _) ->
      true
  | t ->
      if acc then true else sfold_tm_tm (tm_has_side_effect nmap) acc t

(* Help function that collects all variables in a term *)
let rec collect_vars (free : SymbSet.t) = function
  | TmVar (_, _, s) ->
      SymbSet.add s free
  | t ->
      sfold_tm_tm collect_vars free t

(* Helper function that counts the number of lambdas directly below in a term *)
let rec lam_counts n nmap = function
  | TmLam (_, _, _, _, tlam) ->
      lam_counts (n + 1) nmap tlam
  | TmVar (_, _, s) -> (
    match SymbMap.find_opt s nmap with
    | Some (_, _, _, n_lambdas) ->
        n + n_lambdas
    | None ->
        n )
  | _ ->
      n

(* Helper function that counts the number of lambdas directly below in a term. 
   If negative, it needs to be treated as an open let with side effects *)
let rec lambdas_left nmap n se = function
  | TmApp (_, t1, t2) ->
      lambdas_left nmap (n - 1) (tm_has_side_effect nmap se t2) t1
  | TmVar (_, _, s) -> (
    match SymbMap.find_opt s nmap with
    | Some (_, _, se2, n_lambdas) ->
        let left = max 0 (n + n_lambdas) in
        (max 0 (n + n_lambdas), if left > 0 then se else se || se2)
    | None ->
        (0, se) )
  | t ->
      (max 0 n, se || tm_has_side_effect nmap false t)

(* Help function that collects let information and free variables 
   Returns a tuple with two elements
   1. NMap: a mapping from a let symbol to a tuple with the following 4 elements: 
          (a) The symbol set of variables inside the let that points backwards
          (c) Boolean flag saying if the let is used.  
          (b) Boolean stating if the let body has (possibly) side effects
          (d) Lambda count. That is, how many lambdas that are at the top of the body 
   2. Free Vars: A symbol set with all variables that are free (not under a lambda in a let) *)
let collect_in_body s nmap free = function
  | TmLam (_, _, _, _, tlam) ->
      let vars = collect_vars SymbSet.empty tlam in
      (* Note: we need to compute the side effect, if other open terms refer to this term *)
      let se = tm_has_side_effect nmap false tlam in
      (SymbMap.add s (vars, false, se, lam_counts 1 nmap tlam) nmap, free)
  | body ->
      let lambdas, se_free = lambdas_left nmap 0 false body in
      let se_all = tm_has_side_effect nmap false body in
      let vars = collect_vars SymbSet.empty body in
      let used = if lambdas > 0 && not se_free then false else se_all in
      let free = if used then SymbSet.union free vars else free in
      (SymbMap.add s (vars, used, se_all, lambdas) nmap, free)

(* Collect all mappings for lets (mapping symbol name of the let
   to the set of variables in the let body). It also collects
   all variables that are free, not under a lambda in a let *)
let collect_lets nmap t =
  let rec work (nmap, free) = function
    | TmVar (_, _, s) ->
        (nmap, SymbSet.add s free)
    | TmLet (_, _, s, _, t1, t2) ->
        work (collect_in_body s nmap free t1) t2
    | TmRecLets (_, lst, tt) ->
        let f (nmap, free) (_, _, s, _, t) = collect_in_body s nmap free t in
        let nmap, free = List.fold_left f (nmap, free) lst in
        (* Update side effect in recursive lets, dependent on each other *)
        let slst = List.map (fun (_, _, s, _, _) -> s) lst in
        let update orig nmap s =
          let vars, used, _, lambdas = SymbMap.find s nmap in
          if SymbSet.mem orig vars then
            SymbMap.add s (vars, used, true, lambdas) nmap
          else nmap
        in
        let handle_se nmap s =
          let _, _, se, _ = SymbMap.find s nmap in
          if se then List.fold_left (update s) nmap slst else nmap
        in
        let nmap = List.fold_left handle_se nmap slst in
        work (nmap, free) tt
    | t ->
        sfold_tm_tm work (nmap, free) t
  in
  work (nmap, SymbSet.empty) t

(* Returns a new nmap, where it is marked with true everywhere we have
   a let that is used. Use depth-first search (DFS) in the graph with
   color marking. Returns the nmap. *)
let mark_used_lets (nmap, free) =
  let rec dfs s (visited, nmap) =
    if SymbSet.mem s visited then (visited, nmap)
    else
      let visited = SymbSet.add s visited in
      match SymbMap.find_opt s nmap with
      | Some (symset, _, se, n) ->
          let nmap = SymbMap.add s (symset, true, se, n) nmap in
          SymbSet.fold dfs symset (visited, nmap)
      | None ->
          (visited, nmap)
  in
  SymbSet.fold dfs free (SymbSet.empty, nmap) |> snd

(* Removes all lets that have not been marked as 'used'. *)
let rec remove_lets nmap = function
  | TmLet (fi, x, s, ty, t1, t2) -> (
    (* Is the let marked as used? *)
    match SymbMap.find s nmap with
    | _, true, _, _ ->
        TmLet (fi, x, s, ty, t1, remove_lets nmap t2)
    | _ ->
        remove_lets nmap t2 )
  | TmRecLets (fi, lst, tt) ->
      let f (_, _, s, _, _) =
        match SymbMap.find s nmap with _, b, _, _ -> b
      in
      let lst = List.filter f lst in
      if List.length lst = 0 then remove_lets nmap tt
      else TmRecLets (fi, lst, remove_lets nmap tt)
  | t ->
      smap_tm_tm (remove_lets nmap) t

(* Helper function for pretty printing a nmap *)
let pprint_nmap symbmap nmap =
  let f k (ss, used, se, n) acc =
    acc ^. us "let "
    ^. pprint_named_symb symbmap k
    ^. us " -> "
    ^. pprint_named_symbset symbmap ss
    ^. us ", used = "
    ^. us (if used then "true" else "false")
    ^. us ", side_effect = "
    ^. us (if se then "true" else "false")
    ^. us ", #lambdas = "
    ^. us (sprintf "%d" n)
    ^. us "\n"
  in
  SymbMap.fold f nmap (us "")

(* Helper that creates a nmap with side effect info for builtin constants *)
let make_builtin_nmap builtin_sym2term =
  let f acc (s, t) =
    let v =
      (SymbSet.empty, false, tm_has_side_effect SymbMap.empty false t, 0)
    in
    SymbMap.add s v acc
  in
  List.fold_left f SymbMap.empty builtin_sym2term

(* Helper for extending the symbmap wiht built in names *)
let extend_symb_map_builtin builtin_name2sym symbmap =
  let f acc (xsid, s) =
    let x =
      match xsid with IdVar sid -> ustring_of_sid sid | _ -> failwith "error"
    in
    SymbMap.add s x acc
  in
  List.fold_left f symbmap builtin_name2sym

(* The main dead code elimination function 
   of flag utest is false, then utests are also removed
*)
let elimination builtin_sym2term builtin_name2sym t =
  if !disable_dead_code_elimination then t
  else (
    if !enable_debug_dead_code_info then
      _symbmap := extend_symb_map_builtin builtin_name2sym (symbmap t) ;
    (* Collect all lets and store a graph in 'nmap' and free variable in 'free' *)
    let nmap, free = collect_lets (make_builtin_nmap builtin_sym2term) t in
    if !enable_debug_dead_code_info then (
      print_endline "-- Dead code info: collected lets --" ;
      pprint_nmap !_symbmap nmap |> uprint_endline ;
      print_endline "-- Dead code info: free variables --" ;
      pprint_named_symbset !_symbmap free |> uprint_endline ) ;
    (* Mark all lets that are used in the graph *)
    let nmap = mark_used_lets (nmap, free) in
    if !enable_debug_dead_code_info then (
      print_endline "\n-- Dead code info: marked used lets --" ;
      pprint_nmap !_symbmap nmap |> uprint_endline ) ;
    (* Remove all lets that are not used *)
    remove_lets nmap t )