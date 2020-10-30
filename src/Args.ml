let batch = ref false
let debug = ref false
let show  = ref false


let spec =
  [ ( "-b"
    , Arg.Set batch
    , "run as batch and ignore all display")
  ; ( "--batch"
    , Arg.Set batch
    , "run as batch and ignore all display")
  ; ( "-d"
    , Arg.Set debug
    , "output debug information")
  ; ( "--debug"
    , Arg.Set debug
    , "output debug information")
  ; ( "-s"
    , Arg.Set debug
    , "display each computation step")
  ; ( "--show"
    , Arg.Set debug
    , "display each computation step")
  ]

let files = ref []

let anon_fun fn = files := fn :: !files

let usage_msg =
  Printf.sprintf "Usage: %s [args] [f1.pml] ... [fn.pml]" Sys.argv.(0)

let _ = Arg.parse spec anon_fun usage_msg

let files = List.rev !files

(* Some general configuration *)
let _ = Sys.catch_break true
let _ = Printexc.record_backtrace true
