 module type PLUG =
  sig
    val residual : unit -> 'a 
  end
  
let registry = ref None

let register m = registry := Some m

let get_plugin () : (module PLUG)  =
  match !registry with 
  | Some s -> s
  | None -> failwith "No plugin loaded" 

