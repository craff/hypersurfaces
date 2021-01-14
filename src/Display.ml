open Gles3
open Gles3.Type
open Args
module F = Field.Float
module VF = F.V

type gl_object =
  { vert : float_bigarray
  ; norm : float_bigarray
  ; elem : uint_bigarray
  ; col  : float array
  ; view : float array
  ; shape : shape
  ; uid  : int
  ; mutable visible : bool
  }

let mk_object =
  let c = ref 0 in
  (fun vert norm elem col view shape ->
    let uid = !c in
    incr c;
    { vert; norm; elem; col; view; uid; shape; visible=false })

let wait, restart =
  let c = Condition.create () in
  let m = Mutex.create () in
  Mutex.lock m;
  (fun () -> if not !batch then Condition.wait c m),
  (fun () -> Condition.signal c)

let objects = ref ([] : (string * gl_object) list)

let display names =
  List.iter (fun (name, o) ->
      o.visible <-  List.mem name names) !objects

let draw_mutex = Mutex.create ()

type camera =
  { pos : float array
  ; front : float array
  ; up: float array
  ; mutable speed : float
  ; mutable rspeed : float
  ; mutable curve : bool }

let camera =
  { pos = [| 0.0;0.0;-5.0 |]
  ; front = [| 0.0;0.0;1.0 |]
  ; up = [| 0.0;1.0;0.0 |]
  ; speed = 0.1
  ; rspeed = acos(-1.0) *. 1. /. 180.
  ; curve = true }

let camera_right () = VF.(vp camera.front camera.up)

let home () =
  let set v1 v2 = Array.blit v2 0 v1 0 3 in
  set camera.pos [| 0.0;0.0;-5.0 |];
  set camera.front [| 0.0;0.0;1.0 |];
  set camera.up [| 0.0;1.0;0.0 |];
  camera.speed <- 0.1;
  camera.rspeed <- acos(-1.0) *. 1. /. 180.

let move_right () = VF.combq 1. camera.pos camera.speed (camera_right ())
let move_left  () = VF.combq 1. camera.pos (-. camera.speed) (camera_right ())
let move_left  () = VF.combq 1. camera.pos (-. camera.speed) (camera_right ())
let move_up    () = VF.combq 1. camera.pos camera.speed camera.up
let move_down  () = VF.combq 1. camera.pos (-. camera.speed) camera.up
let rotate_right () =
  VF.combq (cos camera.rspeed) camera.front (sin camera.rspeed) (camera_right ())
let rotate_left () =
  VF.combq (cos camera.rspeed) camera.front (-. sin camera.rspeed) (camera_right ())
let rotate_up () =
  let r = Array.copy camera.front in
  VF.combq (cos camera.rspeed) camera.front (sin camera.rspeed) camera.up;
  VF.combq (cos camera.rspeed) camera.up (-. sin camera.rspeed) r
let rotate_down () =
  let r = Array.copy camera.front in
  VF.combq (cos camera.rspeed) camera.front (-. sin camera.rspeed) camera.up;
  VF.combq (cos camera.rspeed) camera.up (sin camera.rspeed) r


let camera_speed () =
  if camera.curve then
    ~-. VF.(camera.pos *.* camera.front) *. camera.speed
  else
    camera.speed
let move_forward () = VF.combq 1. camera.pos (camera_speed ()) camera.front
let move_back  () = VF.combq 1. camera.pos (-. camera_speed ()) camera.front
let accel () = camera.speed <- camera.speed *. 1.5
let slow ()  = camera.speed <- camera.speed /. 1.5
let toggle_curve () =
  camera.curve <- not camera.curve;
  Printf.printf "curve mode is %b\n%!" camera.curve

let add_object = fun name obj ->
  Mutex.lock draw_mutex;
  objects := (name, obj) :: !objects;
  Mutex.unlock draw_mutex

let rm_object = fun obj ->
  Mutex.lock draw_mutex;
  objects := List.filter (fun (_,o) -> o.uid <> obj.uid) !objects;
  Mutex.unlock draw_mutex

(* Initialise the main window. *)
module Init() = struct
let window_width  : int ref   = ref 400 (* Window width.  *)
let window_height : int ref   = ref 400 (* Window height. *)
let window_ratio  : float ref = ref 1.0 (* Window ratio.  *)

let camera_mat () =
  Matrix.lookat camera.pos VF.(camera.pos +++ camera.front) camera.up

let projection () = Matrix.perspective 45.0 !window_ratio 0.1 100.0

let _ =
  Egl.initialize ~width:!window_width ~height:!window_height "test_gles"

(* Shader programs for lines *)
let lines_prg : unit Shaders.program =
  let open Shaders in
  let vertex   = Shaders.of_string gl_vertex_shader Lines_shader.vertex in
  let fragment = Shaders.of_string gl_fragment_shader Lines_shader.fragment in
  compile ("light_shader", [vertex ; fragment])

(* Note that [lines_prg] cannot be used until uniforms and atributes are set. *)

(* We set the uniform parameters of the shader. *)
let lines_prg = Shaders.float4v_cst_uniform lines_prg "lightDiffuse" [|0.8;0.8;0.8;1.0|]

(* We abstract away the "Projection" parameter. *)
let lines_prg = Shaders.float_mat4_uniform lines_prg "Projection"

(* We abstract away the "Camera" parameter. *)
let lines_prg = Shaders.float_mat4_uniform lines_prg "Camera"

(* We abstract away the "ModelView" parameter. *)
let lines_prg = Shaders.float_mat4_uniform lines_prg "ModelView"

(* We abstract away the "Color" parameter. *)
let lines_prg = Shaders.float4v_uniform lines_prg "color"

(* We abstract away the vertices matrix. *)
let lines_prg = Shaders.float_attr lines_prg "in_position"

let draw_line_object cam proj obj =
  Shaders.draw_uint_elements lines_prg gl_lines obj.elem
    obj.vert obj.col obj.view cam proj

let draw_point_object cam proj obj =
  Shaders.draw_uint_elements lines_prg gl_points obj.elem
    obj.vert obj.col obj.view cam proj

(* Shader programs for triangles *)
let triangles_prg : unit Shaders.program =
  let open Shaders in
  let vertex   = Shaders.of_string gl_vertex_shader Triangles_shader.vertex in
  let fragment = Shaders.of_string gl_fragment_shader Triangles_shader.fragment in
  compile ("light_shader", [vertex ; fragment])

(* Note that [triangles_prg] cannot be used until uniforms and atributes are set. *)

(* We set the uniform parameters of the shader. *)
let triangles_prg = Shaders.float1_cst_uniform triangles_prg  "specular"     0.1
let triangles_prg = Shaders.float1_cst_uniform triangles_prg  "shininess"    10.0
let triangles_prg = Shaders.float3v_cst_uniform triangles_prg "lightPos1"     [|3.;1.;-1.0|]
let triangles_prg = Shaders.float3v_cst_uniform triangles_prg "lightPos2"     [|-3.;1.;-1.0|]
let triangles_prg = Shaders.float3v_cst_uniform triangles_prg "lightPos3"     [|0.;-1.;-1.0|]
let triangles_prg = Shaders.float4v_cst_uniform triangles_prg "lightDiffuse" [|0.4;0.4;0.4;1.0|]
let triangles_prg = Shaders.float4v_cst_uniform triangles_prg "lightAmbient" [|0.2;0.2;0.2;1.0|]

(* We abstract away the "Projection" parameter. *)
let triangles_prg = Shaders.float_mat4_uniform triangles_prg "Projection"

(* We abstract away the "ModelView" parameter. *)
let triangles_prg = Shaders.float_mat4_uniform triangles_prg "ModelView"

(* We abstract away the "Camera" parameter. *)
let triangles_prg = Shaders.float_mat4_uniform triangles_prg "Camera"

(* We abstract away the "Color" parameter. *)
let triangles_prg = Shaders.float4v_uniform triangles_prg "color"

(* We abstract away the vertices matrix. *)
let triangles_prg = Shaders.float_attr triangles_prg "in_normal"

(* We abstract away the vertices matrix. *)
let triangles_prg = Shaders.float_attr triangles_prg "in_position"

let draw_triangle_object cam proj obj =
  Shaders.draw_uint_elements triangles_prg gl_triangles obj.elem
    obj.vert obj.norm obj.col obj.view cam proj

let draw_object cam proj (_,obj) =
  if obj.visible then match obj.shape with
  | x when x = gl_triangles -> draw_triangle_object cam proj obj
  | x when x = gl_lines -> draw_line_object cam proj obj
  | x when x = gl_points -> draw_point_object cam proj obj
  | _ -> assert false

(* The main drawing function. *)
let draw : unit -> unit = fun () ->
  Thread.yield ();
  Gles3.clear [gl_color_buffer; gl_depth_buffer];
  Mutex.lock draw_mutex;
  let cam = camera_mat () and proj = projection () in
  List.iter (draw_object cam proj) !objects;
  Mutex.unlock draw_mutex;
  Gles3.show_errors "hypersurfaces";
  Egl.swap_buffers ()

let key_cb ~key ~state ~x ~y =
  let _ = x,y in
  let c = if key < 256 then Char.chr key else Char.chr 0 in
  match key, c with
  | _    , ('n'|'N') -> restart ()
  | 65363, _         -> if state = 0 then move_right () else rotate_right ()
  | 65361, _         -> if state = 0 then move_left () else rotate_left ()
  | 65362, _         -> if state = 0 then move_up () else rotate_up ()
  | 65364, _         -> if state = 0 then move_down () else rotate_down ()
  | _    , ' '       -> move_forward ()
  | _    , ('b'|'B') -> move_back ()
  | _    , ('c'|'C') -> toggle_curve ()
  | _    , ('h'|'H') -> home ()
  | _    , ('q'|'Q') -> Egl.exit_loop ()
  | 65307, _         -> Egl.exit_loop ()
  | _                -> Printf.printf "%d %d\n%!" key state

let init () =
  Sys.catch_break false;
  (* Initialise its viewport. *)
  Gles3.viewport ~x:0 ~y:0 ~w:!window_width ~h:!window_height;
  (* Setup the reshape callback. *)
  let reshape ~width ~height =
    window_width := width; window_height := height;
    window_ratio := (float width) /. (float height);
    Gles3.viewport ~x:0 ~y:0 ~w:width ~h:height
  in
  Egl.set_reshape_callback reshape;
  (* Some initialisation of the OpenGL state. *)
  Gles3.enable gl_depth_test;
  Gles3.disable gl_cull_face;
  Gles3.clear_color Gles3.({r=0.0; g=0.0; b=0.0; a=1.0});
  (* When there is nothing to do, we draw. *)
  Egl.set_idle_callback draw;
  (* Draw once to get exceptions (they are all captured by [main_loop]. *)
  draw ();
  Egl.set_key_press_callback key_cb;
  Egl.main_loop ();
  exit 0
end

let _ =
  if not !batch then
    ignore (Thread.create (fun () -> let open Init () in init ()) ())

module Make(R:Field.SPlus) = struct
  module V = R.V

  let epsilon = 1e-6

  let split_segment f acc x1 x2 =
    let l = [Array.map R.to_float x1;Array.map R.to_float x2] in
    let (lp, ln) = List.partition (fun x -> x.(3) > 0.) l in
    let (lz, ln) = List.partition (fun x -> x.(3) = 0.) ln in
    match (lp,lz,ln) with
    | [x1;x2],[],[] | [],[],[x1;x2] ->
       f acc x1 x2
    | [x1],[x2],[]  | [],[x2],[x1] ->
       let epsilon = if lp = [] then -. epsilon else epsilon in
       let lambda1 = epsilon /. x1.(3) in
       let mu1 = 1. -. lambda1 in
       let y1 = VF.comb lambda1 x1 mu1 x2 in
       f acc x1 y1
    | [x1], _, [x2] ->
       let lambda1 = (epsilon -. x2.(3)) /. (x1.(3) -. x2.(3)) in
       let mu1 = 1. -. lambda1 in
       let lambda2 = (~-. epsilon -. x2.(3)) /. (x1.(3) -. x2.(3)) in
       let mu2 = 1. -. lambda2 in
       let y1 = VF.comb lambda1 x1 mu1 x2 in
       let y2 = VF.comb lambda2 x1 mu2 x2 in
       f (f acc x1 y1) x2 y2
    | _ -> acc

  let split_triangle f acc x1 x2 x3 =
    let l = [Array.map R.to_float x1;Array.map R.to_float x2;Array.map R.to_float x3] in
    let (lp, ln) = List.partition (fun x -> x.(3) > 0.) l in
    let (lz, ln) = List.partition (fun x -> x.(3) = 0.) ln in
    match (lp,lz,ln) with
    | [x1;x2;x3],[],[] | [],[],[x1;x2;x3] ->
       f acc x1 x2 x3
    | [x1;x2],[x3],[] | [],[x3],[x1;x2] ->
       let epsilon = if lp = [] then -. epsilon else epsilon in
       let lambda1 = epsilon /. x1.(3) in
       let mu1 = 1. -. lambda1 in
       let lambda2 = epsilon /. x2.(3) in
       let mu2 = 1. -. lambda2 in
       let y1 = VF.comb lambda1 x1 mu1 x3 in
       let y2 = VF.comb lambda2 x2 mu2 x3 in
       f (f acc x1 x2 y1) x2 y1 y2
    | [x1],[x2;x3],[] | [],[x2;x3],[x1] ->
       let epsilon = if lp = [] then -. epsilon else epsilon in
       let lambda2 = epsilon /. x1.(3) in
       let mu2 = 1. -. lambda2 in
       let lambda3 = epsilon /. x1.(3) in
       let mu3 = 1. -. lambda3 in
       let y2 = VF.comb lambda2 x1 mu2 x2 in
       let y3 = VF.comb lambda3 x1 mu3 x3 in
       f acc x1 y2 y3
    | [x1],[x3],[x2] ->
       let lambda1 = epsilon /. x1.(3) in
       let mu1 = 1. -. lambda1 in
       let lambda2 = -. epsilon /. x2.(3) in
       let mu2 = 1. -. lambda2 in
       let lambda13 = (epsilon -. x2.(3)) /. (x1.(3) -. x2.(3)) in
       let mu13 = 1. -. lambda13 in
       let lambda23 = (-. epsilon -. x2.(3)) /. (x1.(3) -. x2.(3)) in
       let mu23 = 1. -. lambda23 in
       let y1 = VF.comb lambda1 x1 mu1 x3 in
       let y2 = VF.comb lambda2 x2 mu2 x3 in
       let y13 = VF.comb lambda13 x1 mu13 x2 in
       let y23 = VF.comb lambda23 x1 mu23 x2 in
       f (f acc x1 y1 y13) x2 y2 y23
    | [x1;x2], _, [x3] | [x3], _, [x1;x2] ->
       let epsilon = if List.length lp = 1 then -. epsilon else epsilon in
       let lambda1 = (epsilon -. x3.(3)) /. (x1.(3) -. x3.(3)) in
       let mu1 = 1. -. lambda1 in
       let lambda13 = (-. epsilon -. x3.(3)) /. (x1.(3) -. x3.(3)) in
       let mu13 = 1. -. lambda13 in
       let lambda2 = (epsilon -. x3.(3)) /. (x2.(3) -. x3.(3)) in
       let mu2 = 1. -. lambda2 in
       let lambda23 = (-. epsilon -. x3.(3)) /. (x2.(3) -. x3.(3)) in
       let mu23 = 1. -. lambda23 in
       let y1 = VF.comb lambda1 x1 mu1 x3 in
       let y2 = VF.comb lambda2 x2 mu2 x3 in
       let y13 = VF.comb lambda13 x1 mu13 x3 in
       let y23 = VF.comb lambda23 x2 mu23 x3 in
       f (f (f acc x1 x2 y1) x2 y1 y2) x3 y13 y23
    | _ -> acc

  let mk_points_from_polyhedron ?(color=[|1.;1.;1.;1.|]) name p =
    let tbl = Hashtbl.create 1001 in
    let count = ref 0 in
    let (size, p) = List.fold_left (fun (j,acc) a ->
        let d = Array.length a.(0) in
        let a =
          if d < 4 then
            Array.map (fun v -> Array.init 4 (fun i -> if i = 3 then v.(d-1)
                                                       else if i >= d-1 then R.zero
                                                       else v.(i))) a
          else a
        in
        let x1 = a.(0) in
        let fn x =
          let x = Array.map R.to_float x in
          try Hashtbl.find tbl x
          with
            Not_found ->
            let i = !count in
            incr count;
            Hashtbl.add tbl x i;
            i
        in
        (j+1, fn x1::acc)) (0, []) p
    in
    let elem = create_uint_bigarray size in
    List.iteri (fun i i1 ->
        let sete i x = Bigarray.Genarray.set elem [|i|] (Int32.of_int x) in
        sete i i1) p;
    let vert = create_float_bigarray (Hashtbl.length tbl * 3) in
    Hashtbl.iter (fun x i ->
        let setv i x = Bigarray.Genarray.set vert [|i|] x in
        setv (3*i+0) (x.(0)/.x.(3));
        setv (3*i+1) (x.(1)/.x.(3));
        setv (3*i+2) (x.(2)/.x.(3))) tbl;
    let obj =
      mk_object vert vert elem color Matrix.idt gl_points
    in
    add_object name obj;
    obj

  let mk_lines_from_polyhedron ?(color=[|1.;1.;1.;1.|]) name p =
    let tbl = Hashtbl.create 1001 in
    let count = ref 0 in
    let (size, p) = List.fold_left (fun (j,acc) a ->
        let d = Array.length a.(0) in
        let a =
          if d < 4 then
            Array.map (fun v -> Array.init 4 (fun i -> if i = 3 then v.(d-1)
                                                       else if i >= d-1 then R.zero
                                                       else v.(i))) a
          else a
        in
        let x1 = a.(0) in
        let x2 = a.(1) in
        let fn x =
          try Hashtbl.find tbl x
          with
            Not_found ->
            let i = !count in
            incr count;
            Hashtbl.add tbl x i;
            i
        in
        let gn (i,acc) x y =
          (i+1, (fn x, fn y)::acc) in
        split_segment gn (j,acc) x1 x2) (0, []) p
    in
    let elem = create_uint_bigarray (size * 2) in
    List.iteri (fun i (i1,i2) ->
        let sete i x = Bigarray.Genarray.set elem [|i|] (Int32.of_int x) in
        sete (2*i+0) i1;
        sete (2*i+1) i2) p;
    let vert = create_float_bigarray (Hashtbl.length tbl * 3) in
    Hashtbl.iter (fun x i ->
        let setv i x = Bigarray.Genarray.set vert [|i|] x in
        setv (3*i+0) (x.(0)/.x.(3));
        setv (3*i+1) (x.(1)/.x.(3));
        setv (3*i+2) (x.(2)/.x.(3))) tbl;
    let obj =
      mk_object vert vert elem color Matrix.idt gl_lines
    in
    add_object name obj;
    obj

  let mk_triangles_from_polyhedron name p =
    let (size, p) = List.fold_left (fun (j,acc) a ->
        if Array.length a <> 3 && Array.length a <> 4 then invalid_arg "dimension not 3";
        let f (j,acc) x1 x2 x3 =
          let gn (j,acc) x1 x2 x3 = (j+1, (x1,x2,x3)::acc) in
          split_triangle gn (j,acc) x1 x2 x3
        in
        if Array.length a = 3 then
          f (j,acc) a.(0) a.(1) a.(2)
        else
          assert false) (0, []) p
    in
    let elem = create_uint_bigarray (size * 3) in
    let vert = create_float_bigarray (size * 9) in
    let norm = create_float_bigarray (size * 9) in
    List.iteri (fun i (x,y,z) ->
        let sete i x = Bigarray.Genarray.set elem [|i|] (Int32.of_int x) in
        let setv i x = Bigarray.Genarray.set vert [|i|] x in
        let setn i x = Bigarray.Genarray.set norm [|i|] x in
        sete (3*i+0) (3*i+0);
        sete (3*i+1) (3*i+1);
        sete (3*i+2) (3*i+2);
        let a = [| x.(0)/.x.(3); x.(1)/.x.(3); x.(2)/.x.(3)|] in
        let b = [| y.(0)/.y.(3); y.(1)/.y.(3); y.(2)/.y.(3)|] in
        let c = [| z.(0)/.z.(3); z.(1)/.z.(3); z.(2)/.z.(3)|] in
        setv (9*i+0) a.(0); setv (9*i+1) a.(1); setv (9*i+2) a.(2);
        setv (9*i+3) b.(0); setv (9*i+4) b.(1); setv (9*i+5) b.(2);
        setv (9*i+6) c.(0); setv (9*i+7) c.(1); setv (9*i+8) c.(2);
        let n = VF.(normalise (vp (b --- a) (c --- a))) in
        setn (9*i+0) n.(0); setn (9*i+1) n.(1); setn (9*i+2) n.(2);
        setn (9*i+3) n.(0); setn (9*i+4) n.(1); setn (9*i+5) n.(2);
        setn (9*i+6) n.(0); setn (9*i+7) n.(1); setn (9*i+8) n.(2);
      ) p;
    let obj =
      mk_object vert norm elem [|0.2;0.2;0.6;1.0|] Matrix.idt gl_triangles
    in
    add_object name obj;
    obj

end
