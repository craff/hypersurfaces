open Gles3
open Args

type gl_object =
  { vert : float_bigarray
  ; norm : float_bigarray
  ; elem : uint_bigarray
  ; col  : float array
  ; view : float array
  ; uid  : int
  }

let mk_object =
  let c = ref 0 in
  (fun vert norm elem col view ->
    let uid = !c in
    incr c;
    { vert; norm; elem; col; view; uid })

let wait, restart =
  let c = Condition.create () in
  let m = Mutex.create () in
  Mutex.lock m;
  (fun () -> if not !batch then Condition.wait c m),
  (fun () -> Condition.signal c)

let line_objects = ref ([] : gl_object list)
let triangle_objects = ref ([] : gl_object list)

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

module F = Field.Float
module V = Vector.Make(F)

let projection () =
  Matrix.lookat camera.pos V.(camera.pos +++ camera.front) camera.up

let camera_right () = V.(vp camera.front camera.up)

let move_right () = V.combq 1. camera.pos camera.speed (camera_right ())
let move_left  () = V.combq 1. camera.pos (-. camera.speed) (camera_right ())
let move_left  () = V.combq 1. camera.pos (-. camera.speed) (camera_right ())
let move_up    () = V.combq 1. camera.pos camera.speed camera.up
let move_down  () = V.combq 1. camera.pos (-. camera.speed) camera.up
let rotate_right () =
  V.combq (cos camera.rspeed) camera.front (sin camera.rspeed) (camera_right ())
let rotate_left () =
  V.combq (cos camera.rspeed) camera.front (-. sin camera.rspeed) (camera_right ())
let rotate_up () =
  let r = camera_right () in
  V.combq (cos camera.rspeed) camera.front (sin camera.rspeed) camera.up;
  Array.blit camera.up 0 (V.vp camera.front r) 0 3
let rotate_down () =
  let r = camera_right () in
  V.combq (cos camera.rspeed) camera.front (-. sin camera.rspeed) camera.up;
  Array.blit camera.up 0 (V.vp camera.front r) 0 3

let camera_speed () =
  if camera.curve then
    let r = ~-. V.(camera.pos *.* camera.front) *. camera.speed in
    Printf.printf "%f %a\n%!" r V.print_vector camera.pos;
    r
  else
    camera.speed
let move_forward () = V.combq 1. camera.pos (camera_speed ()) camera.front
let move_back  () = V.combq 1. camera.pos (-. camera_speed ()) camera.front
let accel () = camera.speed <- camera.speed *. 1.5
let slow ()  = camera.speed <- camera.speed /. 1.5
let toggle_curve () =
  camera.curve <- not camera.curve;
  Printf.printf "curve mode is %b\n%!" camera.curve

let add_line_object = fun obj ->
  Mutex.lock draw_mutex;
  line_objects := obj :: !line_objects;
  Mutex.unlock draw_mutex

let add_triangle_object = fun obj ->
  Mutex.lock draw_mutex;
  triangle_objects := obj :: !triangle_objects;
  Mutex.unlock draw_mutex

let rm_line_object = fun obj ->
  Mutex.lock draw_mutex;
  line_objects := List.filter (fun o -> o.uid <> obj.uid) !line_objects;
  Mutex.unlock draw_mutex

let rm_triangle_object = fun obj ->
  Mutex.lock draw_mutex;
  triangle_objects := List.filter (fun o -> o.uid <> obj.uid) !triangle_objects;
  Mutex.unlock draw_mutex


(* Initialise the main window. *)
module Init() = struct
let window_width  : int ref   = ref 400 (* Window width.  *)
let window_height : int ref   = ref 400 (* Window height. *)
let window_ratio  : float ref = ref 1.0 (* Window ratio.  *)

let _ =
  Egl.initialize ~width:!window_width ~height:!window_height "test_gles"

(* Shader programs for lines *)
let lines_prg : unit Shaders.program =
  let open Shaders in
  let vertex   = Shaders.of_string `vertex_shader Lines_shader.vertex in
  let fragment = Shaders.of_string `fragment_shader Lines_shader.fragment in
  compile ("light_shader", [vertex ; fragment])

(* Note that [lines_prg] cannot be used until uniforms and atributes are set. *)

(* We set the uniform parameters of the shader. *)
let lines_prg = Shaders.float3v_cst_uniform lines_prg "lightPos"     [|0.0;3.0;10.0|]
let lines_prg = Shaders.float4v_cst_uniform lines_prg "lightDiffuse" [|0.8;0.8;0.8;1.0|]
let lines_prg = Shaders.float4v_cst_uniform lines_prg "lightAmbient" [|0.2;0.2;0.2;1.0|]

(* We abstract away the "ModelView" parameter. *)
let lines_prg : (float array -> unit) Shaders.program =
  Shaders.float_mat4_uniform lines_prg "ModelView"

(* We abstract away the "Projection" parameter. *)
let lines_prg : (float array -> float array -> unit) Shaders.program =
  Shaders.float_mat4_uniform lines_prg "Projection"

(* We abstract away the "Color" parameter. *)
let lines_prg : (float array ->
                 float array -> float array -> unit) Shaders.program =
  Shaders.float4v_uniform lines_prg "color"

(* We abstract away the vertices matrix. *)
let lines_prg : (float_bigarray -> float array ->
                 float array -> float array -> unit) Shaders.program =
  Shaders.float_attr lines_prg "in_position"

let draw_line_object proj obj =
  Shaders.draw_uint_elements lines_prg `lines obj.elem
    obj.vert obj.col proj obj.view

(* Shader programs for triangles *)
let triangles_prg : unit Shaders.program =
  let open Shaders in
  let vertex   = Shaders.of_string `vertex_shader Triangles_shader.vertex in
  let fragment = Shaders.of_string `fragment_shader Triangles_shader.fragment in
  compile ("light_shader", [vertex ; fragment])

(* Note that [triangles_prg] cannot be used until uniforms and atributes are set. *)

(* We set the uniform parameters of the shader. *)
let triangles_prg = Shaders.float1_cst_uniform triangles_prg  "specular"     0.2
let triangles_prg = Shaders.float1_cst_uniform triangles_prg  "shininess"    10.0
let triangles_prg = Shaders.float3v_cst_uniform triangles_prg "lightPos"     [|10.0;10.0;-25.0|]
let triangles_prg = Shaders.float4v_cst_uniform triangles_prg "lightDiffuse" [|0.6;0.6;0.6;1.0|]
let triangles_prg = Shaders.float4v_cst_uniform triangles_prg "lightAmbient" [|0.1;0.1;0.1;1.0|]

(* We abstract away the "ModelView" parameter. *)
let triangles_prg : (float array -> unit) Shaders.program =
  Shaders.float_mat4_uniform triangles_prg "ModelView"

(* We abstract away the "Projection" parameter. *)
let triangles_prg : (float array -> float array -> unit) Shaders.program =
  Shaders.float_mat4_uniform triangles_prg "Projection"

(* We abstract away the "Color" parameter. *)
let triangles_prg : (float array ->
                 float array -> float array -> unit) Shaders.program =
  Shaders.float4v_uniform triangles_prg "color"

(* We abstract away the vertices matrix. *)
let triangles_prg : (float_bigarray -> float array ->
                 float array -> float array -> unit) Shaders.program =
  Shaders.float_attr triangles_prg "in_normal"

(* We abstract away the vertices matrix. *)
let triangles_prg : (float_bigarray -> float_bigarray -> float array ->
                 float array -> float array -> unit) Shaders.program =
  Shaders.float_attr triangles_prg "in_position"

let draw_triangle_object proj obj =
  Shaders.draw_uint_elements triangles_prg `triangles obj.elem
    obj.vert obj.norm obj.col proj obj.view

(* The main drawing function. *)
let draw : unit -> unit = fun () ->
  Thread.yield ();
  Gles3.clear [`color_buffer; `depth_buffer];
  Mutex.lock draw_mutex;
  let (<*>) = Matrix.mul in
  let p = Matrix.perspective 45.0 !window_ratio 0.1 100.0 <*> projection() in
  List.iter (draw_triangle_object p) !triangle_objects;
  List.iter (draw_line_object p) !line_objects;
  Mutex.unlock draw_mutex;
  Gles3.show_errors "hypersurfaces";
  Egl.swap_buffers ()

let key_cb ~key ~state ~x ~y =
  let c = if key < 256 then Char.chr key else Char.chr 0 in
  match key, c with
  | _    , ('n'|'N') -> restart ()
  | 65363, _         -> if state = 0 then move_right () else rotate_right ()
  | 65361, _         -> if state = 0 then move_left () else rotate_left ()
  | 65362, _         -> if state = 0 then move_up () else rotate_up ()
  | 65364, _         -> if state = 0 then move_down () else rotate_down ()
  | _    , ' '       -> move_forward ()
  | _    , ('b'|'B') -> move_back ()
  | _                -> Printf.printf "%d %d\n%!" key state

let init () =
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
  Gles3.enable `depth_test;
  Gles3.disable `cull_face;
  Gles3.clear_color Gles3.({r=0.0; g=0.0; b=0.0; a=1.0});
  (* When there is nothing to do, we draw. *)
  Egl.set_idle_callback draw;
  (* Draw once to get exceptions (they are all captured by [main_loop]. *)
  draw ();
  Sys.catch_break false;
  Egl.set_key_press_callback key_cb;
  Egl.main_loop ()
end

let _ =
  if not !batch then
    ignore (Thread.create (fun () -> let open Init () in init ()) ())

module Make(R:Field.S) = struct
  module V = Vector.Make(R)
  open R
  open V


  let mk_lines_from_polyhedron p =
    let tbl = Hashtbl.create 1001 in
    let count = ref 0 in
    let (size, p) = List.fold_left (fun (j,acc) a ->
        if Array.length a <> 2 then invalid_arg "dimension not 2";
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
        let gn x y = (fn x, fn y) in
        if x1.(2) *. x2.(2) <=. zero then
          begin
            let h = one /. of_int 1_000_000 in
            let lambda1 = (h -. x2.(2)) /. (x1.(2) -. x2.(2)) in
            let mu1 = one -. lambda1 in
            let lambda2 = (~-. h -. x2.(2)) /. (x1.(2) -. x2.(2)) in
            let mu2 = one -. lambda2 in
            let y1 = comb lambda1 x1 mu1 x2 in
            let y2 = comb lambda2 x1 mu2 x2 in
            if x1.(2) >. zero || x2.(2) <. zero then
              (j+2, gn x1 y1 :: gn x2 y2 :: acc)
            else if x1.(2) <. zero || x2.(2) >. zero then
              (j+2, gn x1 y2 :: gn x2 y1 :: acc)
            else
              (j, acc)
          end
        else
           (j+1, gn x1 x2 :: acc)) (0, []) p
    in
    let elem = create_uint_bigarray (size * 2) in
    List.iteri (fun i (i1,i2) ->
        let sete i x = Bigarray.Genarray.set elem [|i|] (Int32.of_int x) in
        sete (2*i+0) i1;
        sete (2*i+1) i2) p;
    let vert = create_float_bigarray (Hashtbl.length tbl * 3) in
    Hashtbl.iter (fun x i ->
        let setv i x = Bigarray.Genarray.set vert [|i|] (R.to_float x) in
        setv (3*i+0) R.(x.(0)/.x.(2));
        setv (3*i+1) R.(x.(1)/.x.(2));
        setv (3*i+2) R.zero) tbl;
    let obj =
      mk_object vert vert elem [|0.7;0.7;1.0;1.0|] Matrix.idt
    in
    add_line_object obj;
    obj

  let mk_triangles_from_polyhedron p normal =
    let tbl = Hashtbl.create 1001 in
    let count = ref 0 in
    let (size, p) = List.fold_left (fun (j,acc) a ->
        if Array.length a <> 3 && Array.length a <> 4 then invalid_arg "dimension not 3";
        let f (j,acc) x1 x2 x3 =
          let fn x =
            try Hashtbl.find tbl x
            with
              Not_found ->
              let i = !count in
              incr count;
              Hashtbl.add tbl x i;
              i
          in
          let gn x y z = (fn x, fn y, fn z) in
          (*        if x1.(2) *. x2.(2) <=. zero then
          begin
            let h =     one /. of_int 1_000_000 in
            let lambda1     = (h -. x2.(2)) /. (x1.(2) -. x2.(2)) in
            let mu1 = one -. lambda1 in
            let lambda2 = (~-. h -. x2.(2)) /. (x1.(2) -. x2.(2)) in
            let mu2 = one -. lambda2 in
            let y1 = comb lambda1 x1 mu1 x2 in
            let y2 = comb lambda2 x1 mu2 x2 in
            if x1.(2) >. zero || x2.(2) <. zero then
              (j+2, gn x1 y1 :: gn x2 y2 :: acc)
            else if x1.(2) <. zero || x2.(2) >. zero then
              (j+2, gn x1 y2 :: gn x2 y1 :: acc)
            else
              (j, acc)
          end
        else
 *)
          (j+1, gn x1 x2 x3 :: acc)
        in
        if Array.length a = 3 then
          f (j,acc) a.(0) a.(1) a.(2)
        else
          (
          f (f (j,acc) a.(0) a.(1) a.(3)) a.(0) a.(2) a.(3)
                      )) (0, []) p
    in
    let elem = create_uint_bigarray (size * 3) in
    List.iteri (fun i (i1,i2,i3) ->
        let sete i x = Bigarray.Genarray.set elem [|i|] (Int32.of_int x) in
        sete (3*i+0) i1;
        sete (3*i+1) i2;
        sete (3*i+2) i3) p;
    let vert = create_float_bigarray (Hashtbl.length tbl * 3) in
    let norm = create_float_bigarray (Hashtbl.length tbl * 3) in
    Hashtbl.iter (fun x i ->
        let setv i x = Bigarray.Genarray.set vert [|i|] (R.to_float x) in
        let setn i x = Bigarray.Genarray.set norm [|i|] (R.to_float x) in
        setv (3*i+0) R.(x.(0)/.x.(3));
        setv (3*i+1) R.(x.(1)/.x.(3));
        setv (3*i+2) R.(x.(2)/.x.(3));
        let g = normalise (normal x) in
        setn (3*i+0) g.(0);
        setn (3*i+1) g.(1);
        setn (3*i+2) g.(2);
      ) tbl;
    let obj =
      mk_object vert norm elem [|0.2;0.2;0.6;1.0|] Matrix.idt
    in
    add_triangle_object obj;
    obj

end
