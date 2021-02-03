let batch = ref false
let cont  = ref false
let show  = ref false
let rmax  = ref (1. /. 3.) (* should depend upon the dim ?*)
let subd  = ref 0
let prog  = ref false
let quick_test = ref true
let debug_string = ref ""

let spec =
  [ ( "-c"
    , Arg.Set cont
    , "continue after display commands")
  ; ( "--continue"
    , Arg.Set cont
    , "continue after display commands")
  ; ( "-b"
    , Arg.Set batch
    , "run as batch and ignore all display")
  ; ( "--batch"
    , Arg.Set batch
    , "run as batch and ignore all display")
  ; ( "-d"
    , Arg.Set_string debug_string
    , "output debug information")
  ; ( "--debug"
    , Arg.Set_string debug_string
    , "output debug information")
  ; ( "--progress"
    , Arg.Set prog
    , "show building of triangulation")
  ; ( "--rmax"
    , Arg.Set_float rmax
    , "maximum distance to center when optimizing vertex position")
  ; ( "--subd"
    , Arg.Set_int subd
    , "number of subdivision to test a simplex")
  ; ( "--qt"
    , Arg.Set quick_test
    , "enable test of scalar product of gradients before quick hull")
  ; ( "--nqt"
    , Arg.Clear quick_test
    , "disable test scalar of product of gradients before quick hull")
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
