(* learning for CHC with multiple predicates *)
open Torch
open Util
open Global                

let false2real() =
  if !hiddenfun=1 then -1.0 else 0.0
   
let data_to_floatlist dl =
  if !mod2 then
    List.fold_right
      (fun d l ->
        match d with
          Float(x) -> x::l
        | Int(n) -> (Float.of_int n)::(Float.of_int (absmod n 2))::l
        | Bool(b) -> (if b then 1.0 else false2real())::l
        | List(_) -> assert false
      )        
      dl
      []
  else
    List.map datum_to_float dl

let d2f d =
  match d with
    Int(n) -> Float.of_int n
  | Bool(b) -> if b then 1.0 else false2real()
  | Float(x) -> x
  | _ -> assert false
              
let m2d dl monomial =
  match monomial with
    Var(i) -> d2f(List.nth dl i)
  | Mod(i,m) -> (match List.nth dl i with
                  Int(k) -> Float.of_int(absmod k m)
                 | _ -> assert false)
  | Mod2(i) ->  (match List.nth dl i with
                  Int(k) -> Float.of_int(absmod k 2)
                 | _ -> assert false)
let data_to_floatargs monomials dl =
  List.map (m2d dl) monomials

let data_to_boolargs bmonomials dl =
  List.map (m2d dl) bmonomials

let data_to_retval l =
  d2f(take_last l)

let dummy = Int(-1)
let d_nth d i =
  match d with
    List(l) -> (try Int(List.nth l i) with Failure _ -> dummy)
  | _ -> d

let datasize0 d =
  match d with
   List(l) -> List.length l
  | _ -> 0
    
                                                              
let dll2ldl dll n =
  let s = list_max (List.map datasize0 dll) in
  let a = List.init n (fun i-> List.map (fun d -> d_nth d i) dll) in
  let c = List.init n (fun i-> if i<s then 1.0 else 0.0) in
  List.combine c a

let datalength dll = list_max (List.map datasize dll)
  
let datalist_to_floatargs monomials dll biases n =
  (* dll2ldl:
      [l1,...,lk,x1,...,xm] -> 
     [(1,[l1[1],...,lk[1],x1,...,xm]);...;(1,(l1[j],...,lk[j],x1,...,xm)]);(0,_);...;(0,_)]
   *)
  let ldl = dll2ldl dll n in    
  Array.of_list
    (List.map
       (fun (_,dl) ->
         Array.of_list ((data_to_floatargs monomials dl)@biases)
       )
       ldl)

let datalist_to_boolargs bms dll n =
  let ldl = dll2ldl dll n in
  Array.of_list
    (List.map
       (fun (c,dl) ->
         Array.of_list (c::(data_to_boolargs bms dl))
       )
       ldl)
  
  
let create_datahash() =
  let register_atom i (p,args) =
    let func = is_func p in
    let tab = Hashtbl.find rawdatatab p in
    let tempid = if func then
                   if i>0 then FP(0) else if i=0 then FI(0) else FN(0) 
                 else if i>0 then P(0) else if i=0 then I(0) else N(0)
    in
      if Hashtbl.mem tab args then () else Hashtbl.add tab args tempid
  in
  let convert_atom (p,args) =
    (*    let tab = Hashtbl.find rawdatatab p in fst(Hashtbl.find tab args) *)
    (p, id_of_atom p args)
  in
  (Hashtbl.iter (fun p _ -> Hashtbl.add rawdatatab p (Hashtbl.create 64)) signatures;
   Hashtbl.iter
     (fun p _ -> if Hashtbl.mem biastab p then ()
                 else Hashtbl.add biastab p (if !poly then [] else !standard_biases))
     signatures;
   (* for the moment, biases are uniform accross predicates *)
   List.iter (register_atom 1) !posc;
   List.iter (register_atom (-1)) !negc;
   List.iter
     (fun (nl,pl) ->
       List.iter (register_atom 0) nl;
       List.iter (register_atom 0) pl) !impc;
   Hashtbl.iter
     (fun p tab ->
       let (kinds,func,monomials,bmonomials) = Hashtbl.find signatures p in
       let rnn = contain_listkind kinds in
       let (pdata,ndata,idata) = Hashtbl.fold
         (fun args atomid (pl,nl,il) ->
           match atomid with
            FP _ -> (args::pl, nl, il)
           | FN _ -> (pl, args::nl, il)
           | FI _ -> (pl, nl, args::il)
           | P _ -> (args::pl, nl, il)
           | N _ -> (pl, args::nl, il)
           | I _ -> (pl, nl, args::il)
         )
         tab
         ([],[],[])
       in
       let pdataarray = Array.of_list pdata in
       let ndataarray = Array.of_list ndata in
       let idataarray = Array.of_list idata in
       let biases = Hashtbl.find biastab p in
       let functensors dataarray =
         let step = ref 1 in
         let t1 =
           if rnn then
             let n = array_max (Array.map datalength dataarray) in
             let _ = (step := n) in
             Tensor.transpose (Tensor.of_float3 ~device:!Global.device
                                 (Array.map
                                    (fun l -> datalist_to_floatargs monomials l biases n)
                                    dataarray)) ~dim0:0 ~dim1:1
                              (* dim0: maximum list length, dim1: # of training data *)
           else
           Tensor.of_float2 ~device:!Global.device
                          (Array.map
                             (fun l -> Array.of_list ((data_to_floatargs monomials l)@biases))
                             dataarray)
         in
         let t2 =
           if rnn then
             Tensor.transpose
               (Tensor.of_float3 ~device:!Global.device
                          (Array.map
                             (fun l -> datalist_to_boolargs bmonomials l !step)
                             dataarray))
               ~dim0:0 ~dim1:1
           else
           Tensor.of_float2 ~device:!Global.device
                          (Array.map
                             (fun l -> Array.of_list (data_to_boolargs bmonomials l))
                             dataarray)
         in
         let t3 =
           Tensor.of_float1 ~device:!Global.device
                          (Array.map
                             (fun l -> (data_to_retval l))
                             dataarray)
         in
         (t1,t2,t3)
       in
       let predtensors dataarray =
         let step = ref 1 in
         let t1 =
           if rnn then
             let n = array_max (Array.map datalength dataarray) in
             let _ = (step := n) in
             Tensor.transpose (Tensor.of_float3 ~device:!Global.device
                                 (Array.map
                                    (fun l -> datalist_to_floatargs monomials l biases n)
                                    dataarray)) ~dim0:0 ~dim1:1
                              (* dim0: maximum list length, dim1: # of training data *)
           else
           Tensor.of_float2 ~device:!Global.device
                          (Array.map
                             (fun l -> Array.of_list ((data_to_floatargs monomials l)@biases))
                             dataarray)
         in
         let t2 =
           if rnn then
             Tensor.transpose
               (Tensor.of_float3 ~device:!Global.device
                          (Array.map
                             (fun l -> datalist_to_boolargs bmonomials l !step)
                             dataarray))
               ~dim0:0 ~dim1:1
           else
           Tensor.of_float2 ~device:!Global.device
                          (Array.map
                             (fun l -> Array.of_list (data_to_boolargs bmonomials l))
                             dataarray)
         in
         (t1,t2)
       in
       let (psize,nsize,isize) =
       (if func then
         let (fpdatatensor,fbptensor,fplabtensor) = functensors pdataarray in
         let (fndatatensor,fbntensor,fnlabtensor) = functensors ndataarray in
         let (fidatatensor,fbitensor,filabtensor) = functensors idataarray in
         let psize = Array.length pdataarray in
         let nsize = Array.length ndataarray in
         let isize = Array.length idataarray in
         (Hashtbl.add fdatatab p ((psize,fpdatatensor,fbptensor,fplabtensor),
                                  (nsize,fndatatensor,fbntensor,fnlabtensor),
                                  (isize,fidatatensor,fbitensor,filabtensor));
          (psize,nsize,isize))
        else
          let (pdatatensor,pbtensor) = predtensors pdataarray in
          let (ndatatensor,nbtensor) = predtensors ndataarray in
          let (idatatensor,ibtensor) = predtensors idataarray in
         let psize = Array.length pdataarray in
         let nsize = Array.length ndataarray in
         let isize = Array.length idataarray in
         (Hashtbl.add datatab p ((psize, pdatatensor, pbtensor),
                                 (nsize, ndatatensor, nbtensor),
                                 (isize, idatatensor, ibtensor));
          (psize,nsize,isize))
       )
       in
       (* assign ids to atoms *)
       for i=0 to psize-1 do
          let y = pdataarray.(i) in
          Hashtbl.replace tab y (P(i));
          Hashtbl.add id2rawdatatab (P(i)) y
       done;
       for i=0 to nsize-1 do
         let y = ndataarray.(i) in
         Hashtbl.replace tab y (N(i));
         Hashtbl.add id2rawdatatab (N(i)) y
       done;
       for i=0 to isize-1 do
         let y = idataarray.(i) in
         Hashtbl.replace tab y (I(i));
         Hashtbl.add id2rawdatatab (I(i)) y
       done
     )
     rawdatatab;
   positives := List.map convert_atom !posc;
   negatives := List.map convert_atom !negc;
   implications := List.map
                     (fun (nl,pl) -> (List.map convert_atom nl, List.map convert_atom pl))
                     !impc
  )

exception UnSat  
exception QueueEmpty
exception Break
type atomic_cons = POS of atom | NEG of atom
let pqueue = ref []
let nqueue = ref []
let enqueue_pos atoms =
  pqueue := List.rev_append atoms !pqueue
let enqueue_neg atoms =
  nqueue := List.rev_append atoms !nqueue
let dequeue_constr() =
  match !pqueue with
    [] ->
    (match !nqueue with
       [] -> raise QueueEmpty
     | (p,arg)::atoms -> (nqueue := atoms; NEG(p,arg)))
  | (p,arg)::atoms -> (pqueue := atoms; POS(p,arg))

let normalize_constr() =
  let ic' =
    List.fold_left
      (fun ic (nl,pl) ->
        let nl' = List.sort_uniq compare nl in
        let pl' = List.sort_uniq compare pl in
        if List.exists (fun x-> List.mem x pl') nl' then
          raise UnSat
        else
          match (nl',pl') with
            ([], []) -> raise UnSat
          | ([], [a]) -> (posc := a::!posc; ic)  (* todo: avoid duplication *)
          | ([a], []) -> (negc := a::!negc; ic)
          | _ -> (nl',pl')::ic
      )
      []
      !impc
  in
  impc := ic'
  
let propagate() =
  (
(* enqueue_pos !positives;
   enqueue_neg !negatives;
 *)
   normalize_constr();
   enqueue_pos !posc;
   enqueue_neg !negc;
   try
     while true do
       let x = dequeue_constr() in
       match x with
         POS(p,arg) ->
          let a = (p,arg) in
          (negc :=
            List.map (fun (a') ->
                if a=a' then
                  (print_string "The following atom occurs both in positive and negative\n";
                   Dataloader.output_atom stdout a; 
                    raise UnSat)
                else a') !negc;
           impc :=
             List.fold_left
               (fun imp (nl,pl) ->
                 let nl' = List.filter (fun a' -> not(a=a')) nl in
                 if nl=nl' then (nl,pl)::imp
                 else if nl'=[]&&pl=[] then raise UnSat
                 else if List.length nl'=1 && pl=[] then
                     let a' = List.hd nl' in
                     (negc := a'::!negc;
                      enqueue_neg [a'];
                      imp)
                 else if nl'=[]&&List.length(pl)=1 then
                     let a' = List.hd pl in
                     (posc := a'::!posc;
                      enqueue_pos [a'];
                      imp)
                 else
                   (nl',pl)::imp
               )
               []
               !impc
          )
       | NEG(p,arg) ->
          let a = (p,arg) in
          (posc :=
            List.map (fun (a') ->
                if a=a' then raise UnSat
                else a') !posc;
           impc :=
             List.fold_left
               (fun imp (nl,pl) ->
                 let pl' = List.filter (fun a' -> not(a=a')) pl in
                 if pl=pl' then (nl,pl)::imp
                 else if nl=[]&&pl'=[] then raise UnSat
                 else if List.length nl=1 && pl'=[] then
                     let a' = List.hd nl in
                     (negc := a'::!negc;
                      enqueue_neg [a'];
                      imp)
                 else if nl=[]&&List.length(pl')=1 then
                     let a' = List.hd pl' in
                     (posc := a'::!posc;
                      enqueue_pos [a'];
                      imp)
                 else
                   (nl,pl')::imp
               )
               []
               !impc
          )
     done
   with QueueEmpty ->
     num_of_constraints := List.length (!posc) + List.length (!negc) + List.length (!impc)
  )
(*                        
  propagate_pos2neg();
  propagate_pos2imp();
  propagate
  let flag = ref false in
  (List.fold_left
     (fun newimpconstr (l,x) ->
       let l' = List.filter (fun y -> not(List.mem y !pos_constr)) l in
       if l=l' then newimpconstr
       else
         (if l'=[] then (flag := true; post_const := x::!pos_constr; newimpconstr)
          else (l',x)::newimpconstr))
     []
     !imp_constr;
   if !flag then propagate()
   else
     let 
 *)
                    
let init() =
  (Hashtbl.clear datatab;
   Hashtbl.clear qualtab;
   Hashtbl.clear predtab;
   Hashtbl.clear modeltab;
   propagate();
   create_datahash();
   )

let out_activation () = match !outfun with
  | 0 -> Nn.Sigmoid
  | 1 -> Nn.Sigmoid
  | 2 -> Nn.Relu
  | 3 -> Nn.Leaky_relu
  | _ -> assert false
       
let linear1fun nodes vs =
  let l1 = Layer.linear vs !hidden_nodes ~activation:(MyLayer.hidden_activation ()) ~use_bias:false ~input_dim:nodes
  in
     Layer.forward l1

let linear1funinit output_dim ~w_init ~input_dim vs =
  let l1 = Layer.linear vs output_dim ~w_init ~activation:(MyLayer.hidden_activation ()) ~use_bias:false ~input_dim
  in
     Layer.forward l1
   
let linear1 nodes vs =
  Layer.linear vs !hidden_nodes ~activation:(MyLayer.hidden_activation ()) ~use_bias:false ~input_dim:nodes 

let poly1 nodes vs =  
  let l11 = MyLayer.poly vs (2*nodes) ~input_dim:nodes in
  let l12 = Layer.linear vs !hidden_nodes ~activation:(MyLayer.hidden_activation ()) ~input_dim:(2*nodes) in 
  fun xs -> l11 xs |> Layer.forward l12
  
let linear2 vs =
  if !layers=2 then 
    if !cnf || !dnf then
      MyLayer.l_nor vs 1 ~input_dim:(!hidden_nodes)
    else
      Layer.forward
        (Layer.linear vs 1 ~activation:(out_activation()) ~use_bias:true ~input_dim:(!hidden_nodes))
  else
    if !cnf || !dnf then
      MyLayer.l_nor vs !hidden_nodes2 ~input_dim:(!hidden_nodes)
    else
      Layer.forward
        (Layer.linear vs !hidden_nodes2 ~activation:(MyLayer.hidden_activation ()) ~use_bias:true ~input_dim:(!hidden_nodes))

let linear3 vs =
  if !cnf then
    MyLayer.l_nor vs 1 ~input_dim:(!hidden_nodes2)
  else if !dnf then
    MyLayer.l_or vs 1 ~input_dim:(!hidden_nodes2)
  else
    Layer.forward
      (Layer.linear vs 1 ~activation:(out_activation()) ~use_bias:true ~input_dim:(!hidden_nodes2))
  
let llayer inputs outputs ?w_init vs =
  let l1 =
    match w_init with
      None ->
       Layer.linear vs outputs ~activation:(MyLayer.hidden_activation ()) ~use_bias:false  ~input_dim:inputs
    | Some init ->
       Layer.linear vs outputs ~activation:(MyLayer.hidden_activation ()) ~use_bias:false ~w_init:init ~input_dim:inputs
  in
     Layer.forward l1

let llayer_noactivation inputs outputs ?w_init vs =
  let l1 =
    match w_init with
      None -> Layer.linear vs outputs ~use_bias:false ~input_dim:inputs
    | Some init ->
       Layer.linear vs outputs ~use_bias:false ~input_dim:inputs ~w_init:init
  in
     Layer.forward l1
   
let blayer inputs binputs outputs ?w_init vs =
  let l1 =
    match w_init with
      None -> MyLayer.l_nor vs outputs ~input_dim:(inputs+2*binputs)

    | Some init ->
        MyLayer.l_nor vs outputs ~w_init:init ~input_dim:(inputs+2*binputs)
  in
  fun inp binp ->
    let binp' = Tensor.(f 1.0 - binp) in
    l1 Tensor.(cat [inp;binp';binp] ~dim:1)
   
let model layer1 layer2 xs =
  (*  Layer.forward layer1 xs |> Layer.forward layer2*)
   layer1 xs |> layer2

let model3 layer1 layer2 layer3 xs =
  (*  Layer.forward layer1 xs |> Layer.forward layer2*)
  layer1 xs |> layer2 |> layer3
let model4 layer1 layer2 layer3 xs bs =
  let cs = layer2 (layer1 xs) bs in
    layer3 cs 

let emodel layer1 layer2 layer3 xs bs =
  let cs = layer2 (layer1 xs) bs in
  let os = layer3 xs in
  let _ = if !save_classification then
            last_classification := cs
  in
   Tensor.(sum_dim_intlist (cs * os) ~dim:(Some [1]) ~keepdim:false ~dtype:(T Float)) 
  
let prepare_models vs =
  let model_id = ref 0 in
  let bias_id = ref 0 in
  Hashtbl.iter
    (fun p (kinds,func,monomials,bmonomials) ->
      if func then
        if contain_listkind kinds then
          let inputs = (List.length monomials)+(List.length (Hashtbl.find biastab p)) in
          let binputs = List.length bmonomials in
          let model_f = MyLayer.l_rnn vs ~input_dim:inputs ~binput_dim:binputs
                           ~output_dim:(!hidden_rnn) ~boutput_dim:(!hidden_brnn)
                           ~hidden1:(!hidden_nodes) ~hidden2:(!hidden_nodes2)
          in
          (
            Hashtbl.replace fmodeltab p (!model_id, !bias_id, model_f);
            model_id := 5 + !model_id;
            bias_id := !bias_id; (* no bias is used *)
          )
        else
          let inputs = (List.length monomials)+(List.length (Hashtbl.find biastab p)) in
          let binputs = List.length bmonomials in
          let layer1 = llayer inputs !hidden_nodes vs in
          let layer2 = blayer !hidden_nodes binputs !hidden_nodes2 vs in
          let layer3 = llayer_noactivation inputs !hidden_nodes2 vs in
          let model_p = emodel layer1 layer2 layer3 in
          (
            Hashtbl.replace fmodeltab p (!model_id, !bias_id,  model_p);
            model_id := 3 + !model_id
          )
      else
          if contain_listkind kinds then
          let inputs = (List.length monomials)+(List.length (Hashtbl.find biastab p)) in
          let binputs = List.length bmonomials in
          let model_p =
            if !bcrnn then
              try
                let t = Hashtbl.find cmatrixtab p in
                  MyLayer.l_bcrnn ?cmatrix:(Some(t)) vs ~input_dim:inputs ~binput_dim:binputs
                           ~output_dim:(!hidden_rnn) ~boutput_dim:(!hidden_brnn)
                           ~hidden1:(!hidden_nodes) ~hidden2:(!hidden_nodes2)
              with Not_found ->
                  MyLayer.l_bcrnn vs ~input_dim:inputs ~binput_dim:binputs
                           ~output_dim:(!hidden_rnn) ~boutput_dim:(!hidden_brnn)
                           ~hidden1:(!hidden_nodes) ~hidden2:(!hidden_nodes2)
            else MyLayer.l_brnn vs ~input_dim:inputs ~binput_dim:binputs
                           ~boutput_dim:(!hidden_brnn)
                           ~hidden1:(!hidden_nodes) ~hidden2:(!hidden_nodes2)
          in
          (
            Hashtbl.replace modeltab p (!model_id, !bias_id, model_p);
            model_id := if !bcrnn then 4 + !model_id else 3+ !model_id;
            bias_id := !bias_id+2; (* two biases are used *)
          )
          else
            let inputs = (List.length monomials)+(List.length (Hashtbl.find biastab p)) in
            let binputs = List.length bmonomials in
            let layer1 = llayer inputs !hidden_nodes vs in
            let layer2 = blayer !hidden_nodes binputs !hidden_nodes2 vs in
            let layer3 = llayer !hidden_nodes2 1 vs in
            let model_p = model4 layer1 layer2 layer3 in
            (
              Hashtbl.replace modeltab p (!model_id, !bias_id,  model_p);
              model_id := 3 + !model_id
            )
    )
    signatures
  
let reset vs =
  let vs' = Var_store.create ~name:"tmp" ~device:!Global.device () in
 ( Hashtbl.iter
     (fun p (_,func, monomials,bms) ->
       if func then
        let inputs = (List.length monomials)+(List.length (Hashtbl.find biastab p)) in
        let binputs = List.length bms in
        let layer1 = llayer inputs !hidden_nodes vs' in
        let layer2 = blayer !hidden_nodes binputs !hidden_nodes2 vs' in
        let layer3 = llayer_noactivation inputs !hidden_nodes2 vs' in
        let model_p = emodel layer1 layer2 layer3 in
        let _ = fun x y -> model_p x y (* dummy *) in ()
       else
         let nodes = (List.length monomials)+(List.length (Hashtbl.find biastab p)) in
         let dummy2 = if !poly then poly1 nodes vs'
                      else linear1fun nodes vs'
         in
         let _ = fun x -> dummy2 x in
         let dummy = linear2 vs' in
         let dummy3 = if !layers=2 then dummy else linear3 vs' in
         let _ = fun x -> dummy3 x in ()
     )
     signatures;
  Var_store.copy ~src:vs' ~dst:vs)
 (*;
  print_string "weights have been reset to:\n";
  show_weight())
  *)

let rec max_index_of_list_aux l ind i a =
  match l with
    [] -> (i,a)
  | x::l' ->
     if x>a then max_index_of_list_aux l' (ind+1) ind x
     else max_index_of_list_aux l' (ind+1) i a
let max_index_of_list l =
  match l with
    [] -> assert false
  | x::l' -> max_index_of_list_aux l' 0 0 x

  
let loss_pos predictions =
  Hashtbl.fold
    (fun p ((psize,ppre),_,_) loss ->
      if is_func p then
        if psize=0 then loss
        else Tensor.(loss + sum (ppre * ppre))
      else
        if psize=0 then loss
        else if !lossfun<=0 then Tensor.(loss - sum (log (max ppre (f 0.00000001))))
        else if !lossfun=1 then Tensor.(loss + sum (f 1. - ppre))
        else Tensor.(loss + sum ((f 1. - ppre)*(f 1. - ppre)))
    )
    predictions
  (Tensor.f 0.)
let loss_neg predictions =
  Hashtbl.fold
    (fun p (_,(nsize,npre),_) loss ->
      if is_func p then
        Tensor.(loss + sum (sigmoid (f 10. * (f 0.5 - npre * npre))))
      else
        if nsize=0 then loss
        else if !lossfun<=0 then Tensor.(loss - sum (log (max (f 1.00000 - npre) (f 0.00000001))))
        else if !lossfun=1 then Tensor.(loss + sum npre)
        else Tensor.(loss + sum (npre * npre))
    )
    predictions
  (Tensor.f 0.)
(*  
let loss_pos predictions =
  List.fold_left
    (fun s atom ->
      let y = get_prediction predictions atom in
      if !lossfun=0 then Tensor.(s - log y)
      else if !lossfun=1 then Tensor.(s + (f 1. - y))
      else
        Tensor.(s + (f 1. - y)* (f 1. - y)))
    (Tensor.f 0.)
    !positives
let loss_neg predictions =     
  List.fold_left
    (fun s atom ->
      let y = get_prediction predictions atom in
      if !lossfun=0 then Tensor.(s - log (f 1. - y))
      else if !lossfun=1 then Tensor.(s + y)
      else
        Tensor.(s + y * y))
    (Tensor.f 0.)
    !negatives
 *)

(* TODO: modification for functions *)
let loss_imp predictions =
  List.fold_left
    (fun s (nl, pl) ->
      if !lossfun< -1 then
        let y0 = List.fold_left
                (fun p a ->
                  let u = get_prediction predictions a in
                  Tensor.(p * (- log (max u (f 0.000001)))))
                Tensor.(f 1.)
                pl
        in
        let y = List.fold_left
                (fun p a ->
                  let u = get_prediction predictions a in
                  Tensor.(p * (- log (max (f 1. - u ) (f 0.0000001)))))
                y0
                nl
        in
          Tensor.(s+y)
(* this loss function does not seem working well 
        let y0 = List.fold_left
                (fun p a ->
                  let u = get_prediction predictions a in
                  Tensor.(p - log u ))
                Tensor.(f 0.)
                pl
        in
        let y = List.fold_left
                (fun p a ->
                  let u = get_prediction predictions a in
                  Tensor.(p * (f 1. - u )))
                y0
                nl
        in
        let z0 = List.fold_left
                (fun p a ->
                  let u = get_prediction predictions a in
                  Tensor.(p - log (f 1. - u )))
                Tensor.(f 0.)
                nl
        in
        let z = List.fold_left
                (fun p a ->
                  let u = get_prediction predictions a in
                  Tensor.(p * u))
                z0
                pl
        in
        Tensor.(s+y+z)
 *)
      else
        let len = List.length nl + List.length pl in
        let y = List.fold_left
                (fun p a ->
                  let u = get_prediction predictions a in
                    Tensor.(p * (f 1. - u ))
                )
                Tensor.(f 1.)
                pl
        in
        let z0 = List.fold_left
                (fun p a ->
                  let u = get_prediction predictions a in
                  Tensor.(p * u)
                )
                y
                nl
        in
        let z = if !lossfun=0 then Tensor.(-log (max (f 1. - z0) (f 0.000001)))
                else if !lossfun=3 then Tensor.(z0 * z0)
                else if !lossfun= -1 then
                  let e = Tensor.f (2. /. (float_of_int len)) in
                  let z0 = Tensor.(exp2 ((log2 z0) * e)) in
                  Tensor.(log (f 1. - log (max (f 1. - z0) (f 0.000001))))
                else
                  z0
        in
        Tensor.(s+z))
    (Tensor.f 0.)
    !implications

(*  
let rec loss_bool_aux x from upto acc =
  if from>upto then acc
  else
    let y = Tensor.select x 0 from in
    let w = Tensor.(y * y * (y - f 1.) * (y - f 1.)) in
    loss_bool_aux x (from+1) upto Tensor.(acc + w)
  
let loss_bool x = loss_bool_aux x 0 (!datasize - 1) (Tensor.f 0.)
 *)
  
let regularizer() =
  let num_of_preds = Hashtbl.length modeltab in
  let names_of_weights1 =
    "weight"::(List.init (num_of_preds - 1) (fun x->"weight_"^(string_of_int(x* !layers))))
  in
  let names_of_weights2 =
    "weight"::(List.init (num_of_preds - 1) (fun x->"weight_"^(string_of_int(x* !layers + 1))))
  in
  let lam1 = Tensor.(f !regularization_factor) in
  let lam2 = Tensor.(f !regularization_factor2) in
  let v = Var_store.all_vars !global_vs in
  let reg1 = 
    List.fold_left
      (fun x wn ->
        let t = List.assoc wn v in
        Tensor.(x + sum (abs t))
      )
      Tensor.(f 0.)
      names_of_weights1
  in
  let reg2 = 
    List.fold_left
      (fun x wn ->
        let t = List.assoc wn v in
        Tensor.(x + sum (abs t))
      )
      Tensor.(f 0.)
      names_of_weights2
  in
    Tensor.(lam1 * reg1 + lam2 * reg2)
  
let loss_all x =
  if !num_of_constraints=0 then Tensor.(f 0.)
  else if !regularization_factor > 0.
  then
    Tensor.(((f !pos_w) * loss_pos x + loss_neg x  + (f !pos_i) * loss_imp x) / (f (float_of_int !num_of_constraints)) + regularizer())
  else
    Tensor.(((f !pos_w) * loss_pos x + loss_neg x  + (f !pos_i) * loss_imp x) / (f (float_of_int !num_of_constraints)));;

let apply_model b =
  let predictions = Hashtbl.create 16 in
  let dummy_tensor = Tensor.of_float2 ~device:!Global.device [|[||]|]  in
  (last_predictions := predictions;
   Hashtbl.iter
     (fun p ((psize, pdata,pbdata),(nsize,ndata,nbdata),(isize,idata,ibdata)) ->
      let _ = if b then history_bexp := [] in
      let (_,_,model_p) = Hashtbl.find modeltab p in
      let ppre = if psize>0 then model_p pdata pbdata else dummy_tensor in
      let npre = if nsize>0 then model_p ndata nbdata else dummy_tensor in
      let ipre = if isize>0 then model_p idata ibdata else dummy_tensor in
      Hashtbl.replace predictions p ((psize,ppre), (nsize,npre), (isize, ipre));
      if b then
        ((* Printf.printf "registering cexp info for %s\n" p; *)
         Hashtbl.replace last_bexp_examples p !history_bexp)
    )
    datatab;
   Hashtbl.iter
    (fun p ((psize, pdata,bpdata,plabs),(nsize,ndata,bndata,nlabs),(isize,idata,bidata,ilabs)) ->
      let _ = if b then history_cexp := [] in
      let (_,_,model_p) = Hashtbl.find fmodeltab p in
      let ppre = if psize>0 then Tensor.(model_p pdata bpdata - plabs) else dummy_tensor in
      (*      let _ = let shape = Tensor.size ppre in print_string ("Shape: "^(string_of_shape shape)^"\n") in *)
      let npre = if nsize>0 then Tensor.(model_p ndata bndata - nlabs) else dummy_tensor in
      let ipre = if isize>0 then Tensor.(model_p idata bidata - ilabs) else dummy_tensor in
      Hashtbl.replace predictions p ((psize,ppre), (nsize,npre), (isize, ipre));
      if b then
        ((* Printf.printf "registering cexp info for %s\n" p; *)
         Hashtbl.replace last_cexp_examples p !history_cexp)
    )
    fdatatab;
   predictions
  )

let step optm b =
  let _ = if b then save_classification := true in
  let x = apply_model b in
  let _ = save_classification := false in
  let loss = loss_all x in
  let _ = Optimizer.backward_step optm ~loss in
  (loss,x)

let print_array3 a =
 ( print_string "[";
  Array.iter (fun (x,y,z) -> (print_string ("("^(string_of_float x)^","^(string_of_float y)^","^(string_of_float z)^");\n"))) a;
  print_string "]\n")

let print_array4 a =
 ( print_string "[";
  Array.iter (fun (x,y,z,w) -> (print_string ("("^(string_of_float x)^","^(string_of_float y)^","^(string_of_float z)^","^(string_of_float w)^")\n"))) a;
  print_string "]\n")

let print_weight_aux_sub ((a,b),weight) =
  (print_string "(";
   Array.iter (fun y -> print_string ((string_of_float y)^", ")) a;
   print_string ((string_of_float b)^", "^(string_of_float weight)^")\n"))
  
let print_weight_aux a =
  (print_string "[";
   Array.iter print_weight_aux_sub  a;
   print_string "]\n")

let show_tensor s t =
  print_string (s^":\n");
  let dim = List.length(Tensor.size t) in
  if dim=0 then
    let w = Tensor.to_float0_exn t in
    print_float w
  else if dim=1 then
    let w = Tensor.to_float1_exn t in
    print_floatarray w
  else if dim=2 then
    let w = Tensor.to_float2_exn t in
    print_floatarray2 w
  else
    let w = Tensor.to_float3_exn t in
    print_floatarray3 w;
  print_string "\n"

  
let show_weight_f v p =
  let (id,_,_) = Hashtbl.find fmodeltab p in
  if is_rnn p then
    let name_of_weight0 = if id=0 then "weight" else ("weight_"^(string_of_int id)) in
    (*    let name_of_bias = if id=0 then "bias" else ("bias_"^(string_of_int bid)) in *)
    let name_of_weight1 = "weight_"^(string_of_int (1+ id)) in
    let name_of_weight2 = "weight_"^(string_of_int (2+ id)) in
    let name_of_weight3 = "weight_"^(string_of_int (3+ id)) in
    let name_of_weight4 = "weight_"^(string_of_int (4+ id)) in
    let t0 = Base.List.Assoc.find_exn v name_of_weight0 ~equal:Base.String.(=) in
    let t1 = Base.List.Assoc.find_exn v name_of_weight1 ~equal:Base.String.(=)  in
    let t2 = Base.List.Assoc.find_exn v name_of_weight2 ~equal:Base.String.(=)  in
    let t3 = Base.List.Assoc.find_exn v name_of_weight3 ~equal:Base.String.(=) in
    let t4 = Base.List.Assoc.find_exn v name_of_weight4 ~equal:Base.String.(=)  in
    (*    let t5 = Base.List.Assoc.find_exn v name_of_bias ~equal:Base.String.(=) in *)
    (show_tensor name_of_weight0 t0;
     show_tensor name_of_weight1 t1;
     show_tensor name_of_weight2 t2;
     show_tensor name_of_weight3 t3;
     show_tensor name_of_weight4 t4
    )
    
  else
    let name_of_weight0 = if id=0 then "weight" else ("weight_"^(string_of_int id)) in
    let name_of_weight1 = "weight_"^(string_of_int (1+ id)) in
    let name_of_weight2 = "weight_"^(string_of_int (2+ id)) in
    let t0 = Base.List.Assoc.find_exn v name_of_weight0 ~equal:Base.String.(=) in
    let t1 = Base.List.Assoc.find_exn v name_of_weight1 ~equal:Base.String.(=)  in
    let t2 = Base.List.Assoc.find_exn v name_of_weight2 ~equal:Base.String.(=)  in
    (show_tensor name_of_weight0 t0;
     show_tensor name_of_weight1 t1;
     show_tensor name_of_weight2 t2)

let show_weight_p v p =
  let (id,bid,_) = Hashtbl.find modeltab p in
  if is_rnn p then
    let name_of_weight0 = if id=0 then "weight" else ("weight_"^(string_of_int id)) in
    (*    let name_of_bias = if id=0 then "bias" else ("bias_"^(string_of_int bid)) in *)
    let name_of_weight1 = "weight_"^(string_of_int (1+ id)) in
    let name_of_weight2 = "weight_"^(string_of_int (2+ id)) in
    let t0 = Base.List.Assoc.find_exn v name_of_weight0 ~equal:Base.String.(=) in
    let t1 = Base.List.Assoc.find_exn v name_of_weight1 ~equal:Base.String.(=)  in
    let t2 = Base.List.Assoc.find_exn v name_of_weight2 ~equal:Base.String.(=)  in
    (*    let t5 = Base.List.Assoc.find_exn v name_of_bias ~equal:Base.String.(=) in *)
    (show_tensor name_of_weight0 t0;
     show_tensor name_of_weight1 t1;
     show_tensor name_of_weight2 t2;
     if !bcrnn then
      let name_of_weight3 = "weight_"^(string_of_int (3+ id)) in
      let t3 = Base.List.Assoc.find_exn v name_of_weight3 ~equal:Base.String.(=)  in
      let name_of_bias1 = if id=0 then "bias" else ("bias_"^(string_of_int bid)) in
      let name_of_bias3 = "bias_"^(string_of_int (bid+1)) in
      let t4 = Base.List.Assoc.find_exn v name_of_bias1 ~equal:Base.String.(=) in
      let t5 = Base.List.Assoc.find_exn v name_of_bias3 ~equal:Base.String.(=) in
      (show_tensor name_of_weight3 t3;
       show_tensor name_of_bias1 t4;
       show_tensor name_of_bias3 t5;
      )
      else ();
    )
  else
    let name_of_weight0 = if id=0 then "weight" else ("weight_"^(string_of_int (id* !layers))) in
    let name_of_weight1 = "weight_"^(string_of_int (1+ id* !layers)) in
    let name_of_bias = if id=0 then "bias" else ("weight_"^(string_of_int id)) in
    let t0 = Base.List.Assoc.find_exn v name_of_weight0 ~equal:Base.String.(=) in
    let w0 = Tensor.to_float2_exn t0 in
    let w1 = Base.List.Assoc.find_exn v name_of_weight1 ~equal:Base.String.(=)  in
    let w12 = if !layers=2 then
                (show_tensor name_of_weight0 t0;
                 show_tensor name_of_weight1 w1;
                 Tensor.to_float2_exn w1)
              else
                let name_of_weight2 = "weight_"^(string_of_int (2+ id*3)) in
                let w2 = Base.List.Assoc.find_exn v name_of_weight2 ~equal:Base.String.(=)  in
                let w12t = Tensor.(mm (abs w2) (abs w1) ) in
                (show_tensor name_of_weight0 t0;
                 show_tensor name_of_weight1 w1;
                 show_tensor name_of_weight2 w2;
                 Tensor.to_float2_exn w12t)
    in
    let ba = if !poly then
               Tensor.to_float1_exn (List.assoc name_of_bias v)
             else
               Array.make (Array.length w0) 0.
    in
    let _ = if !poly then
              let a= Base.Array.map (Tensor.to_float2_exn (List.assoc "exponent" v))
                       ~f:(fun earray ->
                         Base.Array.map earray ~f:(fun e -> Float.to_int(Float.round(e))))
              in Hashtbl.replace exptab p a
    in
    let rvec = Base.Array.zip_exn (Base.Array.zip_exn w0 ba) w12.(0) in
    let _ = Array.sort(fun (_,w1) (_, w2) -> Float.compare (Float.abs w2) (Float.abs w1))  rvec in
    ((*Qualifiers.extract_qualifiers p rvec; *)
     print_weight_aux rvec)

let show_weight vs =
  let v = Var_store.all_vars vs in
  Hashtbl.iter (fun p _ -> show_weight_p v p) modeltab;
  Hashtbl.iter (fun p _ -> show_weight_f v p) fmodeltab

let rescale_weight_f v p =
  let (id,_,_) = Hashtbl.find fmodeltab p in
  let name_of_weight0 =
    if id=0 then "weight" else ("weight_"^(string_of_int (id* !layers))) in
  let t0 = Base.List.Assoc.find_exn v name_of_weight0 ~equal:Base.String.(=) in
  Tensor.(t0 *= f 1.1)
  
let rescale_weights() =
  let v = Var_store.all_vars !global_vs in
  Hashtbl.iter (fun p _ -> rescale_weight_f v p) fmodeltab

  
let distill _ = assert false (* to do *)

(** obsolete function for debugging
let show_prediction() =
  Hashtbl.iter
    (fun p datatensor ->
      print_string ("Predicate "^p^":\n");
      let (_,model) = Hashtbl.find modeltab p in
      let labels = Tensor.to_float2_exn (model datatensor) in
      let x = Tensor.to_float2_exn datatensor in
      let xl = Base.Array.zip_exn x labels in
      Array.iter
        (fun (x,l) ->
          print_floatarray x;
          print_string ": ";
          print_floatarray l;
          print_string "\n")
        xl)
    datatab
 **)
  
let accuracy_pos predictions =
  let pc = !positives in
  let n = List.length pc in
    let correct =
    List.fold_left
      (fun m atom -> if is_func (pred_of_atom atom)
                     then
                       let x = get_prediction predictions atom in
                       if Float.abs(Tensor.to_float0_exn x)<0.5
                       then m+1 else m
                     else
                       if Tensor.to_float0_exn (get_prediction predictions atom)>0.6
                       then m+1 else m)
      0
      pc
    in (n, correct)
(*         
         (Float.of_int correct) /. (Float.of_int n)
 *)
     
let accuracy_neg predictions =
  let nc = !negatives in
  let n = List.length nc in
    let correct =
    List.fold_left
      (fun m atom -> if is_func (pred_of_atom atom)
                     then
                       if Float.abs(Tensor.to_float0_exn (get_prediction predictions atom))>0.5
                       then m+1 else m
                     else if Tensor.to_float0_exn (get_prediction predictions atom)<0.4
                     then m+1 else m)
      0
      nc
    in (n, correct)

let accuracy_imp predictions =
  let ic = !implications in
  let n = List.length ic in
    let correct =
    List.fold_left
      (fun m (nl,pl) ->
        if List.exists
             (fun a ->
               if is_func (pred_of_atom a)
               then Float.abs(Tensor.to_float0_exn (get_prediction predictions a))>0.5
               else Tensor.to_float0_exn (get_prediction predictions a)<0.4)
             nl
           || List.exists
                (fun a ->
                  if is_func (pred_of_atom a)
                  then Float.abs(Tensor.to_float0_exn (get_prediction predictions a))<0.5
                  else Tensor.to_float0_exn (get_prediction predictions a)>0.6)
                pl
        then m+1 else m)
      0
      ic
    in (n, correct)

let get_statistics() =
  let _ =  save_classification := true in
  let prediction = apply_model true in
  let _ =  save_classification := false in
  let loss = loss_all prediction in
  (last_loss := Tensor.float_value loss;
   Stdio.printf "loss: %f\n" !last_loss;
   let (n1,c1) = accuracy_pos prediction in
   let (n2,c2) = accuracy_neg prediction in
   let (n3,c3) = accuracy_imp prediction in
   (Stdio.printf "accuracy: %d/%d (pos), %d/%d (neg), %d/%d (imp)\n" c1 n1 c2 n2 c3 n3;
    last_imp_miss := n3-c3)
  )

  
     
exception Done
exception Retry
let recent_fail = ref 0
let rec fit numepochs optm =
  try
    for i=0 to numepochs do
      let b = (i mod 1000 = 0) in
      let (loss,prediction) = step optm b in
      if b then
        (Stdio.printf "epochs: %d\n" i;
         last_loss := Tensor.float_value loss;
         Stdio.printf "loss: %f\n" !last_loss;
         let (n1,c1) = accuracy_pos prediction in
         let (n2,c2) = accuracy_neg prediction in
         let (n3,c3) = accuracy_imp prediction in
         Stdio.printf "accuracy: %d/%d (pos), %d/%d (neg), %d/%d (imp)\n" c1 n1 c2 n2 c3 n3;
         flush stdout;
         last_miss := (n1+n2+n3)-(c1+c2+c3);
         last_imp_miss := n3-c3;
         if !last_miss=0 && !last_loss < !loss_threshold
         then sharpen_booleans := true else sharpen_booleans := false;
         if !last_miss=0 && !cut_training && !last_loss < 0.1 *. !loss_threshold
         then raise Done (* finish if the current loss is well below the threshold *)
         else
           if i> numepochs/3 && !last_miss > 5 && !retry>0 then raise Retry
           else if i> numepochs/2 && !last_miss > 0 && !retry>0 then raise Retry
        )
    done;
    if !last_miss=0 (* && !last_loss < !loss_threshold *) then true
    else if !retry>0
    then (recent_fail := !recent_fail + 1;
          if !recent_fail > 2 then
            (* if there are repeated failures, that may be due to a wrong choice of cmatrix;
               we reset cmatrixtab when there are three consecutive failures of convergence *)   
            (Hashtbl.clear cmatrixtab; recent_fail := 0);
          raise Retry)
    else false
  with Done -> true
     | Retry -> 
         (print_string "Learning has not completed: retrying\n";
          retry := !retry - 1;
          recent_fail := 0;
          let vs' = Var_store.create ~name:"tmp" ~device:!Global.device () in
          prepare_models vs';
          global_vs := vs';
          let optm = if !optimizer = 0 then Optimizer.adam vs' ~learning_rate:!learning_rate
                     else if !optimizer=1 then Optimizer.sgd vs' ~learning_rate:!learning_rate
                     else Optimizer.rmsprop vs' ~learning_rate:!learning_rate
          in
          fit !epochs optm
         )

let show_history_cexp() =
  print_string ("logs of cexp\n");
  Hashtbl.iter
    (fun p h ->
      print_string (p^":\n");
      let rnnstates = Array.init !hidden_rnn (fun _ -> []) in
      List.iter
        (fun (inp, binp, bs, out, bout) ->
          for i=0 to !hidden_rnn - 1 do
            rnnstates.(i) <- (List.nth out i, List.nth bout 0)::rnnstates.(i)
          done;
          print_floatlist inp;
          print_floatlist binp;
          print_floatlist bs;
          print_floatlist out;
          print_floatlist bout;
          print_string "\n")
        h
      (*
      print_string "values occurring in rnnstates\n";
      for i=0 to !hidden_rnn - 1 do
        print_floatpairlist rnnstates.(i)
      done
       *)
    )
    last_bexp_examples;
  Hashtbl.iter
    (fun p h ->
      print_string (p^":\n");
      List.iter
        (fun (inp, binp, bs, out, bout) ->
          print_floatlist inp;
          print_floatlist binp;
          print_floatlist bs;
          print_floatlist out;
          print_floatlist bout;
          print_string "\n")
        h
    )
    last_cexp_examples

             
let rec learnsub numepochs vs =
  let optm = if !optimizer = 0 then Optimizer.adam vs ~learning_rate:!learning_rate
           else if !optimizer=1 then Optimizer.sgd vs ~learning_rate:!learning_rate
             else Optimizer.rmsprop vs ~learning_rate:!learning_rate
  in 
  (let _ = match !load with
       Some(file) ->
        let ckptfile=file^".ckpt" in
        (Serialize.load_multi_ ~named_tensors:(Var_store.all_vars vs) ~filename:ckptfile;
         get_statistics();
         true)
     | None -> fit numepochs optm
   in
   let _ = match !save with
       Some(file) ->
        let ckptfile=file^".ckpt" in
        Serialize.save_multi ~named_tensors:(Var_store.all_vars vs) ~filename:ckptfile
    | None -> ()
   in
   show_history_cexp();
   show_weight vs;
   if Qualifiers.construct_functions() then ()
   else
     (print_string "Program extraction was not successful\n";
      if !retry>0 then
        (print_string "Retrying\n";
         retry := !retry - 1;
         let vs' = Var_store.create ~name:"tmp" ~device:!Global.device () in
         prepare_models vs';
         global_vs := vs';
         learnsub numepochs vs'
        )
     )
     
(*   
   print_string "Qualifiers:\n";
   Qualifiers.print_qualifiers();
   (try (
        Qualifiers.construct_predicates();
        print_string "Predicates found:\n";
        Qualifiers.print_predicates()
   )
   with Qualifiers.FAIL _ ->
   if success then
     print_string "Failed to find predicates\n"
   else
     print_string "Learning has not completed\n");
   if !layers=3 && (!cnf || !dnf) && !distflag && success then
     if distill vs then
       (print_string "distilling\n";
        load := None; retry := 0;
        Hashtbl.clear qualtab;
        Hashtbl.clear predtab;
        learnsub numepochs !global_vs)
     else ()
 *)
  )
             
let learn numepochs =
  let _ = init() in
(*  
  let vs = Var_store.create ~name:"parameters" ~device:!Global.device () in
 *)
  let vs = Var_store.create ~name:"parameters" ~device:!Global.device () in
  let _ = (global_vs := vs) in
  let _ = prepare_models vs in
  learnsub numepochs vs
       

let print_options() =
  Printf.printf "Options:\n";
  Printf.printf "  -epochs <num>: set the number of epochs to <num>\n";
  Printf.printf "  -4l: set the number of layers to 4 (default: 3)\n";
  Printf.printf "  -nor: use 'nor-nor' layers for the 3rd and 4th layers\n";
  Printf.printf "  -cnf: use 'nor-nor' layers for the 3rd and 4th layers\n";
  Printf.printf "  -dnf: use 'nor-or' layers for the 3rd and 4th layers\n";
  Printf.printf "  -nodes <num>: set the number of hidden nodes in the second layer to <num> (default: 32)\n";
  Printf.printf "  -nodes2 <num>: set the number of hidden nodes in the third layer to <num> (default: 4)\n";
  Printf.printf "  -qce <num>: set the constant error bound for qualifiers to <num> (default: 1)\n";
  Printf.printf "  -loss <num>: set the loss function  (default: 0)\n";
  Printf.printf "               0: log\n";
  Printf.printf "               1: linear\n";
  Printf.printf "               2: square\n";
  Printf.printf "  -mod2: enable the mod2 operation\n";
  Printf.printf "  -threshold <float num>: stop training when the accuracy is 100%% and the loss becomes smaller than <float num> (default 1e-4)\n";
  Printf.printf "  -nocut: repeat epochs even if the loss becomes below the threshold\n";
  Printf.printf "  -ratio <float num>: set the ratio of hidden nodes considered based on their priorities (default: 1.0)\n";
  Printf.printf "  -abias <num>: add the constant bias input <num>\n";
  Printf.printf "  -bias <num>: replace the constant bias input with <num> (default: 1)\n";
  Printf.printf "  -retry <num>: the number of retries when learning fails (default: 3)\n";
  Printf.printf "  -save <filename>: save the trained NN in <filename>.ckpt\n";
  Printf.printf "  -load <filename>: load the trained NN from <filename>.ckpt\n";
  Printf.printf "  -reg <float num1> <float num2>: add L1 regularization with the coefficients <num1> for the weights in the first layer and <num2> for those in the second layer\n"
  
  
let rec read_options index =
  match Sys.argv.(index) with
    "-epochs" -> (epochs := int_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-distill" -> (distflag := true; read_options (index+1))
  | "-nor" -> (cnf := true; read_options (index+1))
  | "-cnf" -> (cnf := true; layers := 3; read_options (index+1))
  | "-dnf" -> (dnf := true; layers := 3; read_options (index+1))
  | "-v" -> (verbose := true; read_options (index+1))
  | "-bcrnn" -> (bcrnn := true; read_options (index+1))
  | "-brnn" -> (bcrnn := false; read_options (index+1))
  | "-nodes" -> (hidden_nodes := int_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-nodes2" -> (hidden_nodes2 := int_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-rnodes" -> (hidden_rnn := int_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-rbnodes" -> (hidden_brnn := int_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-qce" -> (qcerror := int_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-loss" -> (lossfun := int_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-lossimp" -> (pos_i := float_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-mod2" -> (mod2 := true; read_options (index+1))
  | "-nocut" -> (cut_training := false; read_options (index+1))
  | "-4l" -> (layers := 3; read_options (index+1))
  | "-poly" -> (poly := true; read_options (index+1))
  | "-opt" -> (optimizer := int_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-logqual" -> (log_qual := Some(Sys.argv.(index+1)); read_options (index+2))
  | "-save" -> (save := Some(Sys.argv.(index+1)); read_options (index+2))
  | "-load" -> (load := Some(Sys.argv.(index+1)); read_options (index+2))
  | "-rate" -> (learning_rate := float_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-reg" -> (regularization_factor := float_of_string(Sys.argv.(index+1));
               regularization_factor2 := float_of_string(Sys.argv.(index+2));
               read_options (index+3))
  | "-bfactor" -> (scaling_factor_for_booleans := float_of_string(Sys.argv.(index+1));
                   read_options (index+2))
  | "-cfactor" -> (scaling_factor_for_qlayer := float_of_string(Sys.argv.(index+1));
                   read_options (index+2))
  | "-threshold" -> (loss_threshold := float_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-ratio" -> (ratio_extraction := float_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-retry" -> (retry := int_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-bias" -> (standard_biases := [Float.of_int(int_of_string(Sys.argv.(index+1)))]; read_options (index+2))
  | "-abias" -> (standard_biases := Float.of_int(int_of_string(Sys.argv.(index+1)))::!standard_biases; read_options (index+2))
  | "-hiddenfun" -> (hiddenfun := int_of_string(Sys.argv.(index+1)); read_options (index+2))
  | "-outfun" -> (outfun := int_of_string(Sys.argv.(index+1));
                  if !outfun>1 then lossfun := 2; read_options (index+2))
  | "-o" -> (outfile := Sys.argv.(index+1);read_options (index+2))
  | "--help" -> (print_options(); exit 0)
  | _ -> index
  

let main() =
  let open Format in
  printf "cuda: %b@\n" (Cuda.is_available ());
  (* Global.device := Device.cuda_if_available (); *)
  Global.device := Device.Cpu;
    let index =
      try
        read_options 1
      with Invalid_argument _ -> (print_string "Invalid options\n"; exit(-1))
    in
    let filename = Sys.argv.(index) in
    (Dataloader.input_alldata filename signatures constraints;
     Random.self_init();
     learn !epochs);;

    
if !Sys.interactive then
  ()
else
  main();;
    
(*      
let w = List.assoc "weight_1" (Var_store.all_vars vs)
let loss = Tensor.select x 0 0
let _ = Tensor.backward loss
let _ = Tensor.(grad w)
let _ = Tensor.(no_grad (fun () -> w -= grad w * f 0.01));;
 *)
