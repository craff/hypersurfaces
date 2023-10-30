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
  { safe : float
  ; subd : int
  ; dprec : float
  ; crit : int
  ; crit_limit : float
  ; crit_quality : float
  ; pos_limit : float
  ; zero_limit : float option
  ; zih_limit : float (** if we get a vector vector < zlim, we consider
                          zero to be in the convex hull *)
  ; zih_coef : float (** between 0 and 0.5: 0 we do not ameliorate vector
                         0.5 maximum possible to be decreasing, but may be slow *)
  ; sing_limit : float option
  ; topo : Topology.topo_ask
  ; expected : Topology.topology option
  ; check : bool
  ; certif : bool
  ; project : (int * float) option }

let default_parameters = ref
  { safe = 0.95
  ; subd = 15
  ; dprec = 0.80
  ; crit  = 3
  ; crit_limit = 0.90
  ; crit_quality = 1e-7
  ; pos_limit = 1.25
  ; zero_limit = None
  ; check = false
  ; certif = true
  ; zih_limit = 1.00
  ; zih_coef = 1. /. 4.
  ; sing_limit = None
  ; topo = Topology.Ask_Nbc
  ; expected = None
  ; project = None }

let spec =
  let p = default_parameters in
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
    , Arg.Float (fun x -> p := { !p with safe = x })
    , "minimum determinant required for safety")
  ; ( "--delauney-prec"
    , Arg.Float (fun x -> p := { !p with dprec = x})
    , "minimum visibility to compensate for numerical errors in delauney triangulation")
  ; ( "--subd"
    , Arg.Int (fun n -> p := { !p with subd = n})
    , "number of subdivision to test a simplex")
  ; ( "--nb-critical"
    , Arg.Int (fun n -> p := { !p with crit = n})
    , "number of critical point candidates in a simplex")
  ; ( "--limit-critical"
    , Arg.Float (fun x -> p := { !p with crit_limit = x})
    , "value to consider points to be critical")
  ; ( "--quality-critical"
    , Arg.Float (fun x -> p := { !p with crit_quality = x})
    , "value to consider critical points to be degenerated")
  ; ( "--limit-zero"
    , Arg.Float (fun x -> p := { !p with
                                 zero_limit = if x <= 0. then None else Some x})
    , "value to consider as zero when checking same sign")
  ; ( "--limit-positive"
    , Arg.Float (fun x -> p := { !p with pos_limit = x})
    , "value to consider as zero when checking same sign")
  ; ( "--limit-zih"
    , Arg.Float (fun x -> p := { !p with zih_limit = x})
    , "value to consider gradient tu be zero in the zero in hull test")
  ; ( "--coef-zih"
    , Arg.Float (fun x -> p := { !p with zih_coef = x})
    , "value in [0,0.5] to stop ameliorating certificate when zero not in hull")
  ; ( "--sing-limit"
    , Arg.Float (fun x -> p := if x <= 0. then
                                 { !p with sing_limit = None }
                               else
                                 { !p with sing_limit = Some x;
                                           certif = false})
    , "value to consider to eliminate samll gradient and accept singularities")
  ; ( "--check-triangulation"
    , Arg.Bool (fun b -> p := { !p with check = b })
    , "check some coherence propereties of the final triangulation")
  ; ( "--check-certificate"
    , Arg.Bool (fun b -> p := { !p with certif = b})
    , "do not check the topology with exact rational arithmetic")
  ; ( "--topo-components"
    , Arg.Unit (fun () -> p := { !p with topo = Topology.Ask_Nbc})
    , "compute only the number of connected components of each variety")
  ; ( "--topo-euler"
    , Arg.Unit (fun () -> p := { !p with topo = Topology.Ask_Euler})
    , "compute only the number of connected components of each variety")
  ; ( "--topo-betti"
    , Arg.Unit (fun () -> p := { !p with topo = Topology.Ask_Betti})
    , "compute only the number of connected components of each variety")
  ; ( "--db"
    , Arg.String (fun s -> dbname := Some s)
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
