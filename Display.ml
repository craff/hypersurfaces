open Graphics

module Make(R:Field.S) = struct
  open R

  let init = ref false

  let display : type a. float -> float * float -> a list -> (a -> R.t array array) -> unit =
    fun scale (x0,y0) ls fn ->
    if not !init then
      begin
        let _ = open_graph "" in
        init := true
      end;
    let open Stdlib in
    let w = size_x () and h = size_y () in
    let draw_segment v1 v2 =
      let ([|x1;y1;z1|], [|x2;y2;z2|]) = if cmp v2.(2) zero = 0 then (v2,v1) else (v1,v2) in
      let x1' = to_float x1 in
      let y1' = to_float y1 in
      let z1' = to_float z1 in
      let x2' = to_float x2 in
      let y2' = to_float y2 in
      let z2' = to_float z2 in
      match cmp z1 zero, cmp z2 zero with
      | (0,0) -> ()
      | (_,0) -> assert false
      | (0,_) ->
         let a = int_of_float (scale *. (x2'/.z2' -. x0)) + w/2 in
         let b = int_of_float (scale *. (y2'/.z2' -. y0)) + h/2 in
         let x1 = x1' /. sqrt(x1'*.x1' +. y1'*.y1') in
         let y1 = y1' /. sqrt(x1'*.x1' +. y1'*.y1') in
         let l1,c0 = if x1 > 0.0 then float (w - a),w else (float (-a)),0 in
         let l2,d0 = if y1 > 0.0 then float (h - b),h else (float (-b)),0 in
         let d1 = b + int_of_float (l1 *. y1 /. x1) in
         let c2 = a + int_of_float (l2 *. x1 /. y1) in
         if y1 = 0.0 || c2 < 0 || c2 > w then
           draw_segments [|a,b,c0,d1|]
         else
           draw_segments [|a,b,c2,d0|]
      | _ ->
         let a = int_of_float (scale *. (x1'/.z1' -. x0)) + w/2 in
         let b = int_of_float (scale *. (y1'/.z1' -. y0)) + h/2 in
         let c = int_of_float (scale *. (x2'/.z2' -. x0)) + w/2 in
         let d = int_of_float (scale *. (y2'/.z2' -. y0)) + h/2 in
         draw_segments [|a,b,c,d|]


    in
    List.iter (fun x ->
        let v  = fn x in
        draw_segment v.(0) v.(Array.length v - 1);
        for i = 0 to Array.length v - 2  do
          draw_segment v.(i) v.(i+1);
        done) ls

end
