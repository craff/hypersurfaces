open Format

let batch = ref false
let cont  = ref false
let show  = ref false
let prog  = ref false
let progw  = ref false
let dbname = ref None
let vname = ref ""
let defs = ref []
type precision = Double | Gmp of int
let precision = ref Double

let debug_string = ref ""

type parameters =
  { mutable safe : float
  ; mutable subd : int
  ; mutable dprec : float
  ; mutable crit : int
  ; mutable crit_limit : float
  ; mutable pos_limit : float
  ; mutable zih_limit : float
  ; mutable topo : Topology.topo_ask
  ; expected : Topology.topology option
  ; mutable check : bool
  ; mutable certif : bool
  ; mutable project : (int * float) option }

let default_parameters =
  { safe = 0.95
  ; subd = 15
  ; dprec = 0.80
  ; crit  = 3
  ; crit_limit = 0.90
  ; pos_limit = 1.00
  ; check = false
  ; certif = true
  ; zih_limit = 1.00
  ; topo = Ask_Nbc
  ; expected = None
  ; project = None }

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
  ; ( "--safe"
    , Arg.Float (fun p -> default_parameters.safe <- p)
    , "minimum determinant required for safety")
  ; ( "--delauney-prec"
    , Arg.Float (fun p -> default_parameters.dprec <- p)
    , "minimum visibility to compensate for numerical errors in delauney triangulation")
  ; ( "--subd"
    , Arg.Int (fun p -> default_parameters.subd <- p)
    , "number of subdivision to test a simplex")
  ; ( "--nb-critical"
    , Arg.Int (fun p -> default_parameters.crit <- p)
    , "number of critical point candidates in a simplex")
  ; ( "--limit-critical"
    , Arg.Float (fun p -> default_parameters.crit_limit <- p)
    , "value to consider of point to be critical")
  ; ( "--limit-positive"
    , Arg.Float (fun p -> default_parameters.pos_limit <- p)
    , "value to consider of point to be critical")
  ; ( "--limit-zih"
    , Arg.Float (fun p -> default_parameters.zih_limit <- p)
    , "value to consider of point to be critical")
  ; ( "--check-triangulation"
    , Arg.Bool (fun p -> default_parameters.check <- p)
    , "check some coherence propereties of the final triangulation")
  ; ( "--check-certificate"
    , Arg.Bool (fun p -> default_parameters.certif <- p)
    , "do not check the topology with exact rational arithmetic")
  ; ( "--topo-components"
    , Arg.Unit (fun () -> default_parameters.topo <- Ask_Nbc)
    , "compute only the number of connected components of each variety")
  ; ( "--topo-euler"
    , Arg.Unit (fun () -> default_parameters.topo <- Ask_Euler)
    , "compute only the number of connected components of each variety")
  ; ( "--topo-betti"
    , Arg.Unit (fun () -> default_parameters.topo <- Ask_Betti)
    , "compute only the number of connected components of each variety")
  ; ( "--db"
    , Arg.Tuple [Arg.String (fun s -> printf "Set db: %s\n%!" s;
                                      dbname := Some s)
               ; Arg.Unit (fun () -> default_parameters.topo <- Ask_Betti)]
    , "DB name to store result")
  ; ( "-D"
    , Arg.Tuple [Arg.String (fun s -> vname := s)
               ; Arg.Float (fun f -> defs := (!vname, f) :: !defs)]
    , "Define a variable with a float value from the command line")
  ; ( "--double"
    , Arg.Unit (fun () -> precision := Double)
    , "Use double for computation")
  ; ( "--gmp"
    , Arg.Int (fun n -> precision := Gmp n)
    , "Use gmp with given precision for computation")
  ; ( "--init-rand"
    , Arg.Unit (fun () -> Random.self_init ())
    , "initialize the random generator")
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
