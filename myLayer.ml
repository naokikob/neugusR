open Torch
open Global
open Util 

let hidden_activation () = match !hiddenfun with
  | 0 -> Nn.Sigmoid
  | 1 -> Nn.Tanh
  | 2 -> Nn.Relu
  | 3 -> Nn.Leaky_relu
  | _ -> assert false

let dummy x = string_of_shape x   
let poly vs ?w_init ~input_dim output_dim =
  let w =
    let shape = [ output_dim; input_dim ] in
    match w_init with
    (*    | None -> Var_store.new_var vs ~shape ~init:(Normal {mean=1.0; stdev=1.5}) ~name:"exponent" *)
    | None -> Var_store.new_var vs ~shape ~init:(Uniform (-1., 3.)) ~name:"exponent"
    | Some init -> Var_store.new_var vs ~shape ~init ~name:"exponent"
  in
  let apply =
       fun xs -> Tensor.(exp (mm (log xs) (tr w))) 
  in
    apply 

let l_nor vs ?w_init ~input_dim output_dim =
  let w =
    let shape = [ output_dim; input_dim ] in
    match w_init with
    (*    | None -> Var_store.new_var vs ~shape ~init:(Normal {mean=1.0; stdev=1.5}) ~name:"exponent" *)
    | None -> Var_store.new_var vs ~shape ~init:(Uniform (0., 2.)) ~name:"weight"
    | Some init -> Var_store.new_var vs ~shape ~init ~name:"weight"
  in
  let apply =
    fun xs ->
    let n = List.hd (Tensor.size xs) in
    let xs' = Tensor.reshape xs ~shape:[n; 1; input_dim] in
    let u = Tensor.(sigmoid (f 8.0 * (f 2.0 - xs' * w))) in
    Tensor.(prod_dim_int u ~dim:2 ~keepdim:false ~dtype:(T Float))
  in
    apply 

let l_or vs ?w_init ~input_dim output_dim =
  let w =
    let shape = [ output_dim; input_dim ] in
    match w_init with
    (*    | None -> Var_store.new_var vs ~shape ~init:(Normal {mean=1.0; stdev=1.5}) ~name:"exponent" *)
    | None -> Var_store.new_var vs ~shape ~init:(Uniform (0., 2.)) ~name:"weight"
    | Some init -> Var_store.new_var vs ~shape ~init ~name:"weight"
  in
  let apply =
    fun xs ->
    let n = List.hd (Tensor.size xs) in
    let xs' = Tensor.reshape xs ~shape:[n; 1; input_dim] in
    let u = Tensor.(sigmoid (f (8.0) * (f 2.0 - xs' * w))) in
    Tensor.(f 1.0 - prod_dim_int u ~dim:2 ~keepdim:false ~dtype:(T Float))
  in
    apply 

let discretize_bexp_inout (inp,binp,hb,outs, bouts,cb) =
  let inpa = Array.map Array.to_list (Tensor.to_float2_exn inp) in
  let binpa = Array.map (fun a -> (Array.to_list a)) (Tensor.to_float2_exn binp) in
  let hba = Array.map (fun a -> (Array.to_list a)) (Tensor.to_float2_exn hb) in
  let outsa = Array.map Array.to_list (Tensor.to_float2_exn outs) in
  let boutsa = Array.map Array.to_list (Tensor.to_float2_exn bouts) in
  let controlbits = Tensor.to_float2_exn cb in
  let h = ref [] in
  let n = Array.length inpa in
  for i = 0 to n-1 do
    if controlbits.(i).(0) > 0.5 then
      h := (inpa.(i), binpa.(i), hba.(i), outsa.(i), boutsa.(i))::!h
    else ()
  done;
  !h

let discretize_cexp_inout (inp,binp,hb,outs,bouts) =
  let inpa = Array.map Array.to_list (Tensor.to_float2_exn inp) in
  let binpa = Array.map (fun a -> (Array.to_list a)) (Tensor.to_float2_exn binp) in
  let hba = Array.map (fun a -> (Array.to_list a)) (Tensor.to_float2_exn hb) in
  let outsa = Array.map Array.to_list (Tensor.to_float2_exn outs) in
  let boutsa = Array.map Array.to_list (Tensor.to_float2_exn bouts) in
  let h = ref [] in
  let n = Array.length inpa in
  for i = 0 to n-1 do
    h := (inpa.(i), binpa.(i), hba.(i), outsa.(i), boutsa.(i))::!h
  done;
  !h
  
(* layer for conditional expressions. 4 weights are used *)  
let l_cexp vs ~input_dim ~binput_dim ~output_dim ~boutput_dim ~hidden1 ~hidden2  =
  let qlayer = Layer.forward (Layer.linear vs hidden1 ~activation:Sigmoid ~use_bias:false ~input_dim) in
  let blayer = l_nor vs hidden2 ~input_dim:(hidden1+2*binput_dim) in
  let clayer = Layer.forward (Layer.linear vs (hidden2*output_dim) ~use_bias:false ~input_dim) in
  let boutlayer = l_nor vs boutput_dim ~input_dim:hidden2 in
  fun inp binp ->
  let qs = qlayer inp in
  let binp' = Tensor.(f 1.0 - binp) in
  let bs = blayer Tensor.(cat [qs;binp;binp'] ~dim: 1) in
  let cs = clayer inp in
  let bouts = boutlayer bs in
  let shape = Tensor.size bs in
  let s1 = List.hd shape in 
  let s2 = List.hd (List.tl shape) in
  (* let s2' = s2/output_dim in *)
  (* bs is of size [batchsize;hidden2] and cs is of size [batchsize; hidden2*output_dim]
     reshape bs to [batchsize; 1; hidden2] and cs to [batchsize; output_dim; hidden2]
     and then multiply bs * cs, and take sum on dim 2
   *)
  let bs' = Tensor.(reshape bs ~shape:[s1; 1; s2]) in
  let cs' = Tensor.(reshape cs ~shape:[s1; output_dim; s2]) in
  (*  
  let x = Tensor.(reshape (bs * cs) ~shape:[s1; s2'; output_dim]) in
   *)
  let outs = Tensor.(sum_dim_intlist (bs' * cs') ~dim:[2] ~keepdim:false ~dtype:(T Float)) in
  let _ = if !save_classification then
            history_cexp := discretize_cexp_inout(inp, binp, bs, outs, bouts)
                            @ !history_cexp
  in
  (outs, bouts)

(* layer for boolean expressions. 3 weights are used *)  
let l_bexp vs ~input_dim ~binput_dim ~boutput_dim ~hidden1 ~hidden2  =
  if !cnf then
    let qlayer = Layer.forward (Layer.linear vs hidden1 ~activation:Sigmoid ~use_bias:false ~input_dim) in
    let blayer = l_nor vs hidden2 ~input_dim:(hidden1+2*binput_dim) in
    let boutlayer = l_nor vs boutput_dim ~input_dim:hidden2 in
    fun inp binp cb ->
    let qs = qlayer inp in
    let binp' = Tensor.(f 1.0 - binp) in
    let bs = blayer Tensor.(cat [qs;binp;binp'] ~dim: 1) in
    let bouts = boutlayer bs in
    let _ = if !save_classification then
              history_bexp := discretize_bexp_inout(inp, binp, bs, qs, bouts, cb)
                              @ !history_bexp
    in
    bouts
  else    
    let qlayer = Layer.forward (Layer.linear vs hidden1 ~activation:(hidden_activation ()) ~use_bias:false ~input_dim) in
    let blayer = Layer.forward
                   (Layer.linear vs hidden2 ~activation:(hidden_activation ()) ~input_dim:(hidden1+binput_dim)) in
    let boutlayer =
      if !hiddenfun=2 then
        Layer.forward
          (Layer.linear vs boutput_dim ~activation:Nn.Tanh ~input_dim:hidden2) 
      else
        Layer.forward
          (Layer.linear vs boutput_dim ~activation:(hidden_activation()) ~input_dim:hidden2) 
    in
    fun inp binp cb ->
    let qs = qlayer inp in
    let bs = blayer Tensor.(cat [qs;binp] ~dim: 1) in
    let bouts = boutlayer bs in
    let _ = if !save_classification then
              history_bexp := discretize_bexp_inout(inp, binp, qs, bs, bouts, cb)
                              @ !history_bexp
    in
    bouts

  
(* Tensor[time;batchsize;input_dim] * Tensor[time;batchsize;binput_dim] 
  -> Tensor[batchsize] *)
let l_rnn vs ~input_dim ~binput_dim ~output_dim ~boutput_dim ~hidden1 ~hidden2  =
(*  
  let x = Var_store.new_var vs ~shape:[output_dim] ~init:(Uniform (0., 2.)) ~name:"weight" in
  let y = Var_store.new_var vs ~shape:[boutput_dim] ~init:(Const(-5.)) ~name:"weight" in
  let b = Tensor.(sigmoid y) in
 *)
  let clayer = l_cexp vs ~input_dim:(input_dim+output_dim) ~binput_dim:(binput_dim+boutput_dim)
                 ~output_dim ~boutput_dim ~hidden1 ~hidden2
  in
(*  
  let outlayer = Layer.forward (Layer.linear vs 1 ~use_bias:true ~input_dim:output_dim) in
 *)
  let outlayer =
    let b = Var_store.new_var vs ~shape:[] ~init:(Uniform (-2., 2.)) ~name:"weight" in
    fun xs ->
    let xs0 = Tensor.(select xs ~dim:1 ~index:0) in
    Tensor.(xs0+b) 
  in
  fun xs bs ->
  let shape = Tensor.size xs in
  let bshape = Tensor.size bs in
  let i = List.hd (List.tl (List.tl bshape)) in
  let cb_bs = Tensor.split_with_sizes bs ~split_sizes:[1; i-1] ~dim:2 in (* separate the control bit *)
  let cb = List.hd cb_bs in
  (*
  let _ = Printf.printf "shape of control bits: %s\n" (string_of_shape (Tensor.size cb)) in
  *)
  let bs' = List.hd (List.tl cb_bs) in
  let timespan = List.hd shape in
  let batchsize = List.hd (List.tl shape) in
  (* set the initial values of hidden states to 1 rather than 0, to help hidden values converge to integers *)
  let x = ref (Tensor.zeros [batchsize;output_dim]) in
  let b = ref (Tensor.zeros [batchsize;boutput_dim]) in
  for i=0 to timespan - 1 do
    let xs_i = Tensor.(select xs ~dim:0 ~index:i) in
    let bs_i = Tensor.(select bs' ~dim:0 ~index:i) in
    let cb_i = Tensor.(select cb ~dim:0 ~index:i) in
    let x0 = !x in
    let b0 = !b in
    let (x',b') = clayer (Tensor.(cat [x0; xs_i] ~dim:1)) (Tensor.(cat [b0; bs_i] ~dim:1)) in
(*    
    let _ = Printf.printf "shape of cb_i: %s\n" (string_of_shape (Tensor.size cb_i)) in
    let _ = Printf.printf "shape of x': %s\n" (string_of_shape (Tensor.size x')) in
    let _ = Printf.printf "shape of x0: %s\n" (string_of_shape (Tensor.size x0)) in
    let _ = print_tensor2 cb_i in
 *)
    x := Tensor.(cb_i * x' + (f 1. - cb_i) * x0); (* propagate the result only if the control bit is 1 *)
    b := Tensor.(cb_i * b' + (f 1. - cb_i) * b0)
  done;
  (*
  print_string(string_of_shape(Tensor.size(!x))); 
   *)
  let y = outlayer(!x) in
    y
  (*  print_string(string_of_shape(Tensor.size(y))); *)
      (* Tensor.(select y ~dim:1 ~index:0) *)

let print_shape t =
  let x = Tensor.size t in
  print_string "[";
  List.iter (fun i -> Printf.printf "%d " i) x;
  print_string "]";
  flush stdout
  

(* layer for conditional expressions. 4 weights and 2 biases are used *)  
let l_bcexp ?cmatrix vs ~input_dim ~binput_dim ~output_dim ~boutput_dim ~hidden1 ~hidden2  =
  let qlayer = Layer.forward (Layer.linear vs hidden1 ~activation:(hidden_activation()) ~use_bias:false ~input_dim) in
  let blayer = Layer.forward (Layer.linear vs (hidden2+output_dim)  ~activation:(hidden_activation()) ~input_dim:(hidden1+binput_dim)) in
  let clayer =
    match cmatrix with
      None -> Layer.forward (Layer.linear vs output_dim ~use_bias:false ~input_dim)
    | Some m -> let _ = Layer.linear vs output_dim ~use_bias:false ~input_dim (* dummy *) in
                fun x -> Tensor.mm x m
  in
  let boutlayer = Layer.forward (Layer.linear vs boutput_dim  ~activation:(hidden_activation()) ~input_dim:hidden2) in
  fun inp binp cb ->
  let qs = qlayer (Tensor.(inp * f !scaling_factor_for_qlayer)) in
  let factor = !scaling_factor_for_booleans in
  let qsbinp = Tensor.(cat [qs;binp] ~dim: 1) in
  let bs = blayer Tensor.(qsbinp * f factor) in
  let bs1_bs2 = Tensor.split_with_sizes bs ~split_sizes:[hidden2;output_dim] ~dim:1 in
  let bs1 = List.hd bs1_bs2 in
  let bs2 = List.hd (List.tl bs1_bs2) in
  let bouts = boutlayer (Tensor.(bs1 * f factor)) in
  let cs = clayer inp in
  let outs = if !hiddenfun=1 then
               Tensor.((bs2+f 1.0) * cs / f 2.0)
             else Tensor.(bs2 * cs) in
  let _ = if !save_classification then
            history_bexp := discretize_bexp_inout(inp, qsbinp, bs, outs, bouts, cb)
                            @ !history_bexp
  in
  let booleans = Tensor.(cat [qs;bs2] ~dim:1) in
  (outs, bouts, booleans)
  
(* Tensor[time;batchsize;input_dim] * Tensor[time;batchsize;binput_dim] 
  -> Tensor[batchsize] 
  3(?) weights are used
*)
let l_brnn vs ~input_dim ~binput_dim ~boutput_dim ~hidden1 ~hidden2  =
  let blayer = l_bexp vs ~input_dim:input_dim ~binput_dim:(binput_dim+boutput_dim)
                 ~boutput_dim ~hidden1 ~hidden2
  in
  fun xs bs ->
  let shape = Tensor.size xs in
  let bshape = Tensor.size bs in
  let i = List.hd (List.tl (List.tl bshape)) in
  let cb_bs = Tensor.split_with_sizes bs ~split_sizes:[1; i-1] ~dim:2 in (* separate the control bit *)
  let cb = List.hd cb_bs in
  (*
  let _ = Printf.printf "shape of control bits: %s\n" (string_of_shape (Tensor.size cb)) in
  *)
  let bs' = List.hd (List.tl cb_bs) in
  let timespan = List.hd shape in
  let batchsize = List.hd (List.tl shape) in
  (*  let b = ref (Tensor.zeros [batchsize;boutput_dim]) in *)
  let b = ref (Tensor.ones [batchsize;boutput_dim]) in
  for i=0 to timespan - 1 do
    let xs_i = Tensor.(select xs ~dim:0 ~index:i) in
    let bs_i = Tensor.(select bs' ~dim:0 ~index:i) in
    let cb_i = Tensor.(select cb ~dim:0 ~index:i) in
    let b0 = !b in
    let b' = blayer xs_i (Tensor.(cat [b0; bs_i] ~dim:1)) cb_i in
    b := Tensor.(cb_i * b' + (f 1. - cb_i) * b0)(* propagate the result only if the control bit is 1 *)
  done;
  let b0 = Tensor.(select !b ~dim:1 ~index:0) in
  if !hiddenfun=0 then
    b0
  else
    Tensor.(b0 * f 0.5 + f 0.5) (* [-1,1] -> [0,1] *)

    

  
(* Tensor[time;batchsize;input_dim] * Tensor[time;batchsize;binput_dim] 
  -> Tensor[batchsize] 
  4 weights and 2 biases are used
*)
let l_bcrnn ?cmatrix vs ~input_dim ~binput_dim ~output_dim ~boutput_dim ~hidden1 ~hidden2  =
  let bclayer = l_bcexp ?cmatrix vs ~input_dim:(input_dim+output_dim)
                  ~binput_dim:(binput_dim+boutput_dim)
                  ~output_dim ~boutput_dim ~hidden1 ~hidden2
  in
  fun xs bs ->
  let shape = Tensor.size xs in
  let bshape = Tensor.size bs in
  let i = List.hd (List.tl (List.tl bshape)) in
  let cb_bs = Tensor.split_with_sizes bs ~split_sizes:[1; i-1] ~dim:2 in (* separate the control bit *)
  let cb = List.hd cb_bs in
  (*
  let _ = Printf.printf "shape of control bits: %s\n" (string_of_shape (Tensor.size cb)) in
  *)
  let bs' = List.hd (List.tl cb_bs) in
  let timespan = List.hd shape in
  let batchsize = List.hd (List.tl shape) in
  (*  let b = ref (Tensor.zeros [batchsize;boutput_dim]) in *)
  let b = ref (Tensor.ones [batchsize;boutput_dim]) in
  let x = ref (Tensor.zeros [batchsize;output_dim]) in
  let q = ref (Tensor.zeros [batchsize;hidden1+output_dim]) in
  for i=0 to timespan - 1 do
    let xs_i = Tensor.(select xs ~dim:0 ~index:i) in
    let bs_i = Tensor.(select bs' ~dim:0 ~index:i) in
    let cb_i = Tensor.(select cb ~dim:0 ~index:i) in
    (*
    let _ = Printf.printf "shape of cb_i: %s\n" (string_of_shape (Tensor.size cb_i)) in
     *)
    let b0 = !b in
    let x0 = !x in
    let q0 = !q in
    let (x', b', q') = bclayer
               (Tensor.(cat [x0;xs_i] ~dim:1))
               (Tensor.(cat [b0; bs_i] ~dim:1))
               cb_i
    in
    (* propagate the result only if the control bit is 1 *)
    b := Tensor.(cb_i * b' + (f 1. - cb_i) * b0);
    x := Tensor.(cb_i * x' + (f 1. - cb_i) * x0);
    q := Tensor.(cb_i * q' + (f 1. - cb_i) * q0);
  done;
  (* output the first bit of the internal boolean state *)
  let b0 = Tensor.(select !b ~dim:1 ~index:0) in
  (* force the Boolean states to have values close to -1/1 *)
  let b2 = Tensor.(f 0.5 + f 0.5 * !b * !b) in
  let s = Tensor.(prod_dim_int b2 ~dim:1 ~keepdim:false ~dtype:(T Float)) in
  let b0' = Tensor.(s * b0) in
  let b0'' =
    if !sharpen_booleans then
      let q2 = Tensor.(f 0.95 + f 0.05 * !q * !q) in
      let s' = Tensor.(prod_dim_int q2 ~dim:1 ~keepdim:false ~dtype:(T Float)) in
      Tensor.(s' * b0')
    else b0'
  in
  (* force the integer states to have indeed values close to integers *)
  let b0'' =
    if !sharpen_integers then
      let cosx = Tensor.(cos (f Float.pi * !x)) in
      let s0 = Tensor.(f 0.96875 + f 0.03125 * cosx * cosx) in
      let s1 = Tensor.(prod_dim_int s0 ~dim:1 ~keepdim:false ~dtype:(T Float)) in
      Tensor.(s1 * b0'')
    else b0''
  in
  if !hiddenfun=0 then
    b0'
  else
    Tensor.(b0'' * f 0.5 + f 0.5) (* [-1,1] -> [0,1] *)

    
