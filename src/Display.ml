open Format
open Gles3
open Gles3.Type
open Args
module F = Field.Float
module VF = F.V

let background_color = ref (rgba ~r:1.0 ~g:1.0 ~b:1.0 ~a:1.0)

type gl_object =
  { vert : float_bigarray
  ; norm : float_bigarray
  ; elem : uint_bigarray
  ; col  : float array
  ; view : float array
  ; shape : shape
  ; lwidth : float
  ; uid  : int
  ; mutable visible : bool
  ; mutable deleted : bool
  }

let mk_object =
  let c = ref 0 in
  (fun ?(lwidth=1.0) vert norm elem col view shape ->
    let uid = !c in
    incr c;
    { vert; norm; elem; col; view; uid; shape; lwidth; visible=false; deleted=false })

let objects = ref ([] : (string * gl_object) list)

let updated = ref false

let display_stack = Queue.create ()

let display_mutex  = Mutex.create ()

let display_wait = ref false

let pop_display () =
  try
    Mutex.lock display_mutex;
    let names = Queue.pop display_stack in
    Mutex.unlock display_mutex;
    updated := true;
    display_wait := true;
    objects := List.filter (fun (_, o) -> not o.deleted) !objects;
    List.iter (fun (name, o) ->
        o.visible <-  List.mem name names) !objects;
  with Queue.Empty ->
    Mutex.unlock display_mutex;
    display_wait := false

let display names =
  Mutex.lock display_mutex;
  Queue.push names display_stack;
  Mutex.unlock display_mutex;
  if not !display_wait then (Printf.printf "ICI\n%!"; pop_display ())

let draw_mutex = Mutex.create ()

type camera =
  { pos : float array
  ; front : float array
  ; up: float array
  ; mutable center : float
  ; mutable rspeed : float
  }

let camera =
  { pos = [| 0.0;0.0;5.0 |]
  ; front = [| 0.0;0.0;-1.0 |]
  ; up = [| 0.0;1.0;0.0 |]
  ; center = 5.0
  ; rspeed = acos(-1.0) *. 1. /. 180. }

let camera_right () = VF.(vp camera.front camera.up)

let set v1 v2 = Array.blit v2 0 v1 0 3

let home () =
  updated := true;
  set camera.pos [| 0.0;0.0;5.0 |];
  set camera.front [| 0.0;0.0;-1.0 |];
  set camera.up [| 0.0;1.0;0.0 |];
  camera.center <- 5.0;
  camera.rspeed <- acos(-1.0) *. 1. /. 180.

let camera_speed () = camera.center /. 20.0

let move_right () =
  updated := true;
  VF.combq 1. camera.pos (camera_speed ()) (camera_right ())
let move_left  () =
  updated := true;
  VF.combq 1. camera.pos (-. camera_speed ()) (camera_right ())
let move_up    () =
  updated := true;
  VF.combq 1. camera.pos (camera_speed ()) camera.up
let move_down  () =
  updated := true;
  VF.combq 1. camera.pos (-. camera_speed ()) camera.up
let rotate_right () =
  updated := true;
  VF.combq (cos camera.rspeed) camera.front (sin camera.rspeed) (camera_right ())
let rotate_left () =
  updated := true;
  VF.combq (cos camera.rspeed) camera.front (-. sin camera.rspeed) (camera_right ())
let rotate_up () =
  updated := true;
  let r = Array.copy camera.front in
  VF.combq (cos camera.rspeed) camera.front (sin camera.rspeed) camera.up;
  VF.combq (cos camera.rspeed) camera.up (-. sin camera.rspeed) r
let rotate_down () =
  updated := true;
  let r = Array.copy camera.front in
  VF.combq (cos camera.rspeed) camera.front (-. sin camera.rspeed) camera.up;
  VF.combq (cos camera.rspeed) camera.up (sin camera.rspeed) r
let to_center () =
  set camera.pos (VF.comb 1.0 camera.pos camera.center camera.front);
  set camera.front (VF.opp camera.front)
let crotate_right () =
  to_center (); rotate_right (); to_center ()
let crotate_left () =
  to_center (); rotate_left (); to_center ()
let crotate_up () =
  to_center (); rotate_up (); to_center ()
let crotate_down () =
  to_center (); rotate_down (); to_center ()
let move_forward mc =
  updated := true;
  VF.combq 1. camera.pos (camera_speed ()) camera.front;
  if mc then camera.center <- camera.center -. camera_speed ()
let move_back mc =
  updated := true;
  VF.combq 1. camera.pos (-. camera_speed ()) camera.front;
  if mc then camera.center <- camera.center +. camera_speed ()
let accel () = camera.center <- camera.center *. 1.5
let slow ()  = camera.center <- camera.center /. 1.5

let rm_object = fun obj ->
  Mutex.lock draw_mutex;
  objects := List.filter (fun (_,o) -> o.uid <> obj.uid) !objects;
  updated := true;
  Mutex.unlock draw_mutex

let add_object = fun name obj ->
  Mutex.lock draw_mutex;
  objects := (name, obj) ::
               (List.filter (fun (n,o) -> n <> name ||
                                            (o.deleted <- true;
                                             o.visible)) !objects);
  updated := true;
  Mutex.unlock draw_mutex

let hide_all_objects () =
  let restore = ref (fun () -> ()) in
  List.iter (fun (_,o) ->
      if o.visible then
        begin
          o.visible <- false;
          let old = !restore in
          restore := (fun () -> o.visible <- true; old ())
        end) !objects;
  updated := true;
  !restore

let proj_coef = ref (1. /. 3.)

(* Initialise the main window. *)
module Init() = struct
let window_width  : int ref   = ref 400 (* Window width.  *)
let window_height : int ref   = ref 400 (* Window height. *)
let window_ratio  : float ref = ref 1.0 (* Window ratio.  *)

let camera_mat () =
  Matrix.lookat camera.pos VF.(camera.pos +++ camera.front) camera.up

let projection () =
  Matrix.perspective 45.0 !window_ratio
    (camera.center /. 20.0)
    (camera.center *. 20.0)

let _ =
  let open Egl in
  let config = { red_size = 0
               ; green_size = 0
               ; blue_size = 0
               ; alpha_size = 0
               ; depth_size = 8
               ; stencil_size = 0
               ; samples = 8 }
  in
  initialize ~width:!window_width ~height:!window_height ~config "Hyper"

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
let triangles_prg = Shaders.float1_cst_uniform triangles_prg  "shininess"    8.0
let triangles_prg = Shaders.float3v_cst_uniform triangles_prg "lightPos1"
                      [|0.2;0.2;0.|]
let triangles_prg = Shaders.float3v_cst_uniform triangles_prg "lightPos2"
                      [|-0.2;0.2;0.|]
let triangles_prg = Shaders.float3v_cst_uniform triangles_prg "lightPos3"
                      [|0.0;-0.2;0.|]
let triangles_prg = Shaders.float4v_cst_uniform triangles_prg "lightDiffuse"
                      [|0.4;0.4;0.4;1.0|]
let triangles_prg = Shaders.float4v_cst_uniform triangles_prg "lightAmbient"
                      [|0.2;0.2;0.2;1.0|]

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
  | x when x = gl_lines -> Gles3.line_width obj.lwidth; draw_line_object cam proj obj
  | x when x = gl_points -> draw_point_object cam proj obj
  | _ -> assert false

(* The main drawing function. *)
let draw : unit -> unit = fun () ->
  Gles3.clear_color !background_color;
  Gles3.clear [gl_color_buffer; gl_depth_buffer];
  Mutex.lock draw_mutex;
  let cam = camera_mat () and proj = projection () in
  List.iter (draw_object cam proj) !objects;
  Mutex.unlock draw_mutex;
  Gles3.show_errors "hypersurfaces";
  Egl.swap_buffers ()

let fresh_filename () =
  let fn r = if r = 0 then "image.png"
              else Printf.sprintf "image_%d.png" r
  in
  let rec loop n =
    let fn = fn n in
    if Sys.file_exists fn then loop (n+1) else fn
  in
  loop 0

let save_image () =
  let open Gles3 in
  let width = !window_width in
  let height = !window_height in
  let image =
    { width; height; format = gl_rgba
      ; data = create_ubyte_bigarray (4 * width * height)}
  in
  read_pixels ~x:0 ~y:0 image;
  show_errors "read_pixels";
  let data = image.data in
  let img = Image.create_rgb width height in
  for i = 0 to height - 1 do
    for j = 0 to width - 1 do
      let r = Bigarray.Genarray.get data [|i * 4 * width + 4 * j    |] in
      let g = Bigarray.Genarray.get data [|i * 4 * width + 4 * j + 1|] in
      let b = Bigarray.Genarray.get data [|i * 4 * width + 4 * j + 2|] in
      (*Printf.printf "%d %d: %d %d %d\n%!" j i r g b;*)
      Image.write_rgb img j i r g b
    done
  done;
  let filename = fresh_filename () in
  let file = open_out filename in
  let fn = function
      `String s -> output_string file s; Ok ()
    | `Close -> close_out file; Ok ()
  in
  ImageLib.writefile ~extension:"png" fn img;
  printf "image saved as %S\n%!" filename

let key_cb ~key ~state ~x ~y =
  let state = state land (lnot 16) in (* 16 in numpad lock *)
  let _ = x,y in
  let c = if key < 256 then Char.chr key else Char.chr 0 in
  match key, c with
  | _    , ('n'|'N') -> pop_display ()
  | 65363, _         -> if state = 0 then move_right () else
                          if state = 1 then crotate_right ()
                          else rotate_right ()
  | 65361, _         -> if state = 0 then move_left () else
                          if state = 1 then crotate_left ()
                          else rotate_left ()
  | 65362, _         -> if state = 0 then move_up () else
                          if state = 1 then crotate_up ()
                          else rotate_up ()
  | 65364, _         -> if state = 0 then move_down () else
                          if state = 1 then crotate_down ()
                          else rotate_down ()
  | _    , ' '       -> move_forward (state=0)
  | 65365, _         -> move_forward (state=0)
  | _    , ('b'|'B') -> move_back (state=0)
  | 65366, _         -> move_back (state=0)
  | _    , ('h'|'H') -> home ()
  | _    , ('s'|'S') -> save_image ()
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
    Gles3.viewport ~x:0 ~y:0 ~w:width ~h:height;
    updated := true;
  in
  Egl.set_reshape_callback reshape;
  (* Some initialisation of the OpenGL state. *)
  Gles3.enable gl_depth_test;
  Gles3.disable gl_cull_face;
  Gles3.clear_color Gles3.({r=0.0; g=0.0; b=0.0; a=1.0});
  (* When there is nothing to do, we draw. *)
  Egl.set_idle_callback (fun () -> if !updated then (updated := false; draw ()));
  (* Draw once to get exceptions (they are all captured by [main_loop]. *)
  draw ();
  Egl.set_key_press_callback key_cb;
  Egl.main_loop ();
  exit 0
end

let _ =
  if not !batch then
    ignore (Domain.spawn (fun () -> let open Init () in init ()))

module Make(R:Field.SPlus) = struct
  module V = R.V

  let epsilon = 2e-4

  let zeroest x y = if abs_float x > abs_float y then y else x

  let opp = Array.map (~-.)
  let split_segment f acc x1 x2 =
    let l = [Array.map R.to_float x1;Array.map R.to_float x2] in
    let (lp, lz) = List.partition (fun x -> x.(3) > 0.) l in
    let (ln, lz) = List.partition (fun x -> x.(3) < 0.) lz in
    match (lp,lz,ln) with
    | [x1;x2],[],[] | [x1],[x2],[] ->
       f acc x1 x2
    | [],[],[x1;x2] | [],[x2],[x1] ->
       f acc (opp x1) (opp x2)
    | [], [x1;x2], [] ->
       f (f acc x1 x2) (opp x1) (opp x2)
    | [x1], _, [x2] ->
       let lambda = -. x2.(3) /. (x1.(3) -. x2.(3)) in
       let mu = 1. -. lambda in
       let y1 = VF.comb lambda x1 mu x2 in
       f (f acc x1 y1) (opp x2) (opp y1)
    | _ -> assert false

  let split_triangle f acc x1 x2 x3 =
    let l = [Array.map R.to_float x1;Array.map R.to_float x2;Array.map R.to_float x3] in
    let (lp, lz) = List.partition (fun x -> x.(3) > 0.) l in
    let (ln, lz) = List.partition (fun x -> x.(3) < 0.) lz in
    match (lp,lz,ln) with
    | [x1;x2;x3],[],[] | [x1;x2], [x3], [] | [x1], [x2;x3], [] ->
       f acc x1 x2 x3
    | [],[],[x1;x2;x3] | [], [x1], [x2;x3] | [], [x1;x2], [x3] ->
       f acc (opp x1) (opp x2) (opp x3)
    | [],[x1;x2;x3],[] ->
       f (f acc x1 x2 x3) (opp x1) (opp x2) (opp x3)
    | [x1],[x3],[x2] ->
       let lambda = -. x2.(3) /. (x1.(3) -. x2.(3)) in
       let mu = 1. -. lambda in
       let y1 = VF.comb lambda x1 mu x2 in
       f (f acc x1 y1 x3) (opp x2) (opp y1) (opp x3)
    | [x1;x2], _, [x3] ->
       let lambda1 = -. x3.(3) /. (x1.(3) -. x3.(3)) in
       let mu1 = 1. -. lambda1 in
       let y1 = VF.comb lambda1 x1 mu1 x3 in
       let lambda2 = -. x3.(3) /. (x2.(3) -. x3.(3)) in
       let mu2 = 1. -. lambda2 in
       let y2 = VF.comb lambda2 x2 mu2 x3 in
       f (f (f acc x1 x2 y2) x1 y1 y2) (opp y1) (opp y2) (opp x3)
    | [x3], _, [x1;x2] ->
       let lambda1 = -. x3.(3) /. (x1.(3) -. x3.(3)) in
       let mu1 = 1. -. lambda1 in
       let y1 = VF.comb lambda1 x1 mu1 x3 in
       let lambda2 = -. x3.(3) /. (x2.(3) -. x3.(3)) in
       let mu2 = 1. -. lambda2 in
       let y2 = VF.comb lambda2 x2 mu2 x3 in
       f (f (f acc (opp x1) (opp x2) (opp y2)) (opp x1) (opp y1) (opp y2)) y1 y2 x3
    | _ -> assert false

  let mk_points_from_polyhedron ?(color=[|0.;0.;0.;1.|]) name p =
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
        let d = x.(3) +. !proj_coef in
        setv (3*i+0) (x.(0)/.d);
        setv (3*i+1) (x.(1)/.d);
        setv (3*i+2) (x.(2)/.d)) tbl;
    let obj =
      mk_object vert vert elem color Matrix.idt gl_points
    in
    add_object name obj;
    obj

  let mk_lines_from_polyhedron ?(lwidth=1.0) ?(color=[|0.;0.;0.;1.|]) name p =
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
        let d = x.(3) +. !proj_coef in
        setv (3*i+0) (x.(0)/.d);
        setv (3*i+1) (x.(1)/.d);
        setv (3*i+2) (x.(2)/.d)
      ) tbl;

    let obj =
      mk_object ~lwidth vert vert elem color Matrix.idt gl_lines
    in
    add_object name obj;
    obj

  let mk_triangles_from_polyhedron ?(color=[|0.2;0.2;0.6;1.0|]) name p =
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
        let dx = x.(3) +. !proj_coef in
        let a = [| x.(0)/.dx; x.(1)/.dx; x.(2)/.dx|] in
        let dy = y.(3) +. !proj_coef in
        let b = [| y.(0)/.dy; y.(1)/.dy; y.(2)/.dy|] in
        let dz = z.(3) +. !proj_coef in
        let c = [| z.(0)/.dz; z.(1)/.dz; z.(2)/.dz|] in
        setv (9*i+0) a.(0); setv (9*i+1) a.(1); setv (9*i+2) a.(2);
        setv (9*i+3) b.(0); setv (9*i+4) b.(1); setv (9*i+5) b.(2);
        setv (9*i+6) c.(0); setv (9*i+7) c.(1); setv (9*i+8) c.(2);
        let n = VF.(normalise VF.(vp (b --- a) (c --- b))) in
        setn (9*i+0) n.(0); setn (9*i+1) n.(1); setn (9*i+2) n.(2);
        setn (9*i+3) n.(0); setn (9*i+4) n.(1); setn (9*i+5) n.(2);
        setn (9*i+6) n.(0); setn (9*i+7) n.(1); setn (9*i+8) n.(2);
      ) p;
    let obj =
      mk_object vert norm elem color Matrix.idt gl_triangles
    in
    add_object name obj;
    obj

end
