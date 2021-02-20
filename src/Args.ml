let batch = ref false
let cont  = ref false
let show  = ref false
let rmax  = ref 0.99
let subd  = ref 15
let dprec = ref 1e-14
let prog  = ref false
let progw  = ref false
let debug_string = ref ""
let crit  = ref 5

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
  ; ( "--progress-wait"
    , Arg.(Tuple [Set prog; Set progw])
    , "show building of triangulation and stop at each step")
  ; ( "--rmax"
    , Arg.Set_float rmax
    , "maximum distance to center when optimizing vertex position")
  ; ( "--delauney-prec"
    , Arg.Set_float dprec
    , "minimum visibility to compensate for numerical errors in delauney triangulation")
  ; ( "--subd"
    , Arg.Set_int subd
    , "number of subdivision to test a simplex")
  ; ( "--nb-critical"
    , Arg.Set_int crit
    , "number of critical point candidates in a simplex")
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
