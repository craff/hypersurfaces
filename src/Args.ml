let batch = ref false
let cont  = ref false
let show  = ref false
let prog  = ref false
let progw  = ref false
let debug_string = ref ""


type parameters =
  { mutable rmax : float
  ; mutable subd : int
  ; mutable dprec : float
  ; mutable crit : int }

let default_parameters =
  { rmax = 0.99
  ; subd = 15
  ; dprec = 1e3
  ; crit  = 3 }

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
    , Arg.Float (fun p -> default_parameters.rmax <- p)
    , "maximum distance to center when optimizing vertex position")
  ; ( "--delauney-prec"
    , Arg.Float (fun p -> default_parameters.dprec <- p)
    , "minimum visibility to compensate for numerical errors in delauney triangulation")
  ; ( "--subd"
    , Arg.Int (fun p -> default_parameters.subd <- p)
    , "number of subdivision to test a simplex")
  ; ( "--nb-critical"
    , Arg.Int (fun p -> default_parameters.crit <- p)
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
