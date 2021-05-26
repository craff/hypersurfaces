
let random =
  let iset = ref false
  and gset = ref 0.0
  in
  fun () ->
	if !iset then
	  begin
		iset := false;
		!gset
	  end
	else
	  begin
		let rec loop () =
		  let v1 = 2.0 *. (Random.float 1.0) -. 1.0
		  and v2 = 2.0 *. (Random.float 1.0) -. 1.0
		  in
		  let rsq = v1 *. v1 +. v2 *. v2 in
		  if (rsq >= 1.0) || (rsq = 0.0) then
			loop ()
		  else
			let fac = sqrt (-2.0 *. (log rsq) /. rsq) in
			gset := v1 *. fac;
			iset := true;
			v2 *. fac
		in
		loop ()
	  end
