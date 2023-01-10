open Torch
   
exception TODO
        
(* Global definitions and variables *)
type datum = Int of int | Bool of bool | Float of float | List of int list
type kind = INT | BOOL | FLOAT | LIST
type atom = string * datum list
type vid = int
type monomial = Var of vid | Mod of vid * int  (* v mod n *) | Mod2 of vid

  
type posconstr = atom
type negconstr = atom
type impconstr = atom list * atom list

type constr = posconstr list * negconstr list * impconstr list
(* type fsignature = (string, kind list * monomial list * monomial list) Hashtbl.t *)
type signature = (string, kind list * bool * monomial list * monomial list) Hashtbl.t
(* type signature = fsignature * psignature *)

(* parameters for learning *)
let distflag = ref false
let sharpen_booleans = ref false
let sharpen_integers = ref false
let cnf = ref false
let dnf = ref false
let optimizer = ref 0  (* 0: Adam, 1:Sgd, 2: Rmsprop *)
let lossfun = ref 2 (* 0: log, 1:linear, 2: square with linear imp, 3: square *)
let scaling_factor_for_booleans = ref 2.0
let scaling_factor_for_qlayer = ref 1.0
let use_entropy = ref false
let hiddenfun = ref 1 (* 0: sigmoid, 1: tanh,  *)
let outfun = ref 0 (* 0: sigmoid, 1: sigmoid, 2: leaky_relu, 3: relu *)
let pos_w = ref 1. (* weights on loss functions: loss_all = !pos_w * poss + neg + !pos_i * imp *)
let pos_i = ref 1.
let scale = ref 1. (* factor to normalize input data *)         
let bias = ref false (* bias on 1st layer *)
let bcrnn = ref true
let verbose = ref false
let hidden_nodes = ref 4
let hidden_nodes2 = ref 4
let hidden_rnn = ref 1
let hidden_brnn = ref 1
let layers = ref 2
let learning_rate = ref 1e-3
let regularization_factor = ref 0.
let regularization_factor2 = ref 0.
let bool_threshold = ref 0.5
let epochs = ref 30000
let global_vs = ref (Var_store.create ~name:"tmp" ())
let device = ref Device.Cpu
let loss_threshold = ref 1e-4
let cut_training = ref true
let retry = ref 10
let outfile = ref ""
(* for logging *)
(* filename to save qualifiers *)          
let log_qual: string option ref = ref None
(* filename to save/load NN *)
let save: string option ref = ref None          
let load: string option ref = ref None          
(* for qualifier synthesis *)
(* how much of the weights should be taken into account *)                                
let ratio_extraction = ref 1.0
(* qualifier constant error bound: 
 * when a qualfier candidate a1x1+...anxn+ a0>0 is found, 
 * we add a1x1+...anxn+ a0>c as a candidate for all -e<= c <=e 
 *)
let qcerror = ref 1                     
(* required data
 *  -argument datatab: map from predicates to input data (tensor)
 *  - labtab: map from predicates to the current prediction for input data
 *  - constraints: each atom in the constraints is referred to as (pred, id) 
 *     where id is the index in the tensor of input data;
 *     for example, positive constraints are represented as a list [(pred1,id1); ...]
 *     implication consgtraints are as a list [([(pred1,id1);...], [(pred1',id1);...])]
 *  - bias info: map from predicates to lists of constant inputs [1;10;...]
 *  - signature: map from predicates to their types
 *  - reverse hash table for input data, which maps (pred,id) to the the concrete (typed) 
 *    input data [v1;..;vk]
 *     
 *)

type priority = int
(* qualifier: (coeffs, constant, flag): flag is true for > and false for < *)
type qualifier = int array * int * bool * priority
type exp = int array 
type cond = CondL of exp | CondP of int | CondN of int
type cond_clause = (cond list) * exp
type cexp = cond_clause list               
type dtree = DTbr of cond * dtree * dtree | DTtrue | DTfalse
type cexp2 = dtree * exp
let priority_of_qual quals i = let (_,_,_,p) = List.nth quals i in p
type dnfform = bool list list
let dualqual = ref true
let num_of_candidates = ref 5
let qualtab: (string, qualifier list) Hashtbl.t = Hashtbl.create 16;;
let predtab: (string, dnfform) Hashtbl.t = Hashtbl.create 16;;
let functab: (string, cexp) Hashtbl.t = Hashtbl.create 16;;
let recfunctab: (string, (cond list * exp array * bool array) list * int) Hashtbl.t = Hashtbl.create 16;;
let recpredtab: (string, dtree array * cexp2 array) Hashtbl.t = Hashtbl.create 16;;
let cmatrixtab: (string, Tensor.t) Hashtbl.t = Hashtbl.create 16;;
(* biases added to input data *)           
let standard_biases = ref [1.]
(* whether "mod 2" constraint should be inferred *)
let mod2 = ref false                    
(* whether polynomial constraints should be inferred *)
let poly = ref false
let exptab: (string, int array array) Hashtbl.t = Hashtbl.create 16;;         
(* pred -> predicate-specific biases *)
let biastab: (string, float list) Hashtbl.t = Hashtbl.create 64                    
(* pred -> signature (i.e. list of kinds *)
let signatures: signature = Hashtbl.create 64
(* pred -> input data *)
let arity_of p =
  let (kinds,_,_,_) = Hashtbl.find signatures p in
  List.length kinds
let contain_listkind k =
  List.mem LIST k
let monomials_of p =
  let (_,_,monomials,_) = Hashtbl.find signatures p in monomials
let lookup_kinds (s: signature) p =
  let (kinds,func, _,_) = Hashtbl.find s p in (kinds,func)

let is_func p =
  let (_,func,_,_) = Hashtbl.find signatures p in func
let is_rnn_kind kinds = contain_listkind kinds
let is_rnn p =
  let (kinds,_,_,_) = Hashtbl.find signatures p in is_rnn_kind kinds

                                                
let pred_of_atom atom = fst atom                                                

let earity_of p =
  if !poly then
    2 * List.length (monomials_of p)
  else 
    List.length (monomials_of p)


(* map pred to (size, datatensor); 
 * we keep data occurring in positive, negative, and implication constraints separately
 * to facilitate the computation of loss functions
 *)
let datatab: (string, (int * Tensor.t* Tensor.t)*(int * Tensor.t* Tensor.t)*(int * Tensor.t* Tensor.t) ) Hashtbl.t = Hashtbl.create 64
(* pred -> model *)
let fdatatab: (string, (int * Tensor.t* Tensor.t* Tensor.t)*(int * Tensor.t* Tensor.t* Tensor.t)*(int * Tensor.t* Tensor.t* Tensor.t) ) Hashtbl.t = Hashtbl.create 64
(* pred -> model *)
let modeltab: (string, int * int * (Tensor.t -> Tensor.t-> Tensor.t) ) Hashtbl.t = Hashtbl.create 64
(* func -> model *)
let fmodeltab: (string, int * int * (Tensor.t -> Tensor.t -> Tensor.t) ) Hashtbl.t = Hashtbl.create 64
(* pred -> labes *)
let last_predictions: (string, (int * Tensor.t)*(int * Tensor.t)*(int * Tensor.t)) Hashtbl.t ref = ref (Hashtbl.create 16)
let save_classification = ref false
let last_classification = ref (Tensor.(f 0.))
let last_classifications: (string, Tensor.t) Hashtbl.t = Hashtbl.create 16                
let history_cexp: (float list * float list * float list * float list * float list) list ref
  = ref []
let history_bexp: (float list * float list * float list * float list * float list) list ref
  = ref []
let last_cexp_examples: (string, (float list * float list * float list * float list * float list) list) Hashtbl.t = Hashtbl.create 16
let last_bexp_examples: (string, (float list * float list * float list * float list * float list) list) Hashtbl.t = Hashtbl.create 16
                       
let id_of_pred p =
  try
    let (id,_,_) = Hashtbl.find modeltab p in id
  with
    Not_found ->
    let (id,_,_)= Hashtbl.find fmodeltab p in id
let bid_of_pred p =
  try
    let (_,bid,_) = Hashtbl.find modeltab p in bid
  with
    Not_found ->
    let (_,bid,_)= Hashtbl.find fmodeltab p in bid
                                                                                                 
let last_miss = ref 0
let last_imp_miss = ref 0
let last_loss = ref 1.
let posc: atom list ref = ref []
let negc: atom list ref = ref []
let impc: (atom list * atom list) list ref = ref []
let constraints = (posc, negc, impc)
let num_of_constraints = ref 0
(* the id of atom; 
   it is assigned separately for those occurring in positive, negative, and implication constraints 
   the id is used as an index of the respective data tensor
*)
type atomid = P of int | N of int | I of int | FP of int | FN of int | FI of int
let positives: (string * atomid) list ref = ref []
let negatives: (string * atomid) list ref = ref []
let implications: ((string * atomid) list * (string * atomid) list) list ref = ref []

(* pred -> [v1;...;vk] -> (id, flag) *)
(* id is the identifier of the atom pred(v1,...,vk) *)
(* flag in {-1,0,1}: flag=1 (-1, resp.) means the atom occurs in a positive (negative, resp.) constraint *)
(*                   flag=0 means the atom occurs only in an implication constraint *)
let rawdatatab:
      (string, (datum list, atomid) Hashtbl.t) Hashtbl.t = Hashtbl.create 16
let id2rawdatatab: (atomid, datum list) Hashtbl.t = Hashtbl.create 256
let id_of_atom p args = let tab = Hashtbl.find rawdatatab p in Hashtbl.find tab args
             
(* absmod always returns a positive number *)
(* Note: in ocaml, (-3) mod 2 = -1, but in SMT solver, (-3) mod 2 = 1 *)
let absmod n k = let x = n mod k in if x<0 then x+k else x
               
let string_of_monomial m = 
    match m with
      Var(vid) -> if vid >=0 then "x"^(string_of_int vid)
                  else if vid >= -100 then "r"^(string_of_int (-vid-1))
                  else if vid >= -1000 then "br"^(string_of_int (-(vid+101)))
                  else "qv"^(string_of_int (-(vid+1001)))
    | Mod(vid,n) -> "(x"^(string_of_int vid)^" mod "^(string_of_int n)^")"
    | Mod2(vid) -> "(x"^(string_of_int vid)^" mod 2)"

let get_string_of_monomial monomials i = 
    let m = List.nth monomials i in
    match m with
      Var(vid) -> "x"^(string_of_int vid)
    | Mod(vid,n) -> "(x"^(string_of_int vid)^" mod "^(string_of_int n)^")"
    | Mod2(vid) -> "(x"^(string_of_int vid)^" mod 2)"

let datum_to_float d =
  match d with
    Float(x) -> x
  | Int(n) -> Float.of_int n
  | Bool(b) -> if b then 1.0 else 0.0
  | _ -> assert false
                  
let value_of_monomial p args monomials i =
  if !poly then
    let exponents = (Hashtbl.find exptab p).(i) in
    let s = ref 1. in
    (for j=0 to Array.length(exponents)-1 do
      let m = List.nth monomials j in
        match m with
          Var(vid) ->
             let v = datum_to_float (List.nth args vid) in
             for _=0 to exponents.(j)-1 do
               s := !s *. v
             done
        | Mod(vid,n) ->
           if absmod (Float.to_int (datum_to_float (List.nth args vid))) n =0 then
             s := 0.0
           else ()
        | Mod2(vid) ->
           if absmod (Float.to_int (datum_to_float (List.nth args vid))) 2 =0 then
             s := 0.0
           else ()
     done;
     !s)
  else
    let m = List.nth monomials i in
    match m with
      Var(vid) -> datum_to_float (List.nth args vid)
    | Mod(vid,n) -> Float.of_int(absmod (Float.to_int (datum_to_float (List.nth args vid))) n)
    | Mod2(vid) -> Float.of_int(absmod (Float.to_int (datum_to_float (List.nth args vid))) 2)
                  
let get_prediction_for_atom predictions_for_p id =
  match id with
    P(i) -> let ((_,pred),_,_) = predictions_for_p in
            Tensor.select pred ~dim:0 ~index:i
  | N(i) -> let (_, (_,pred),_) = predictions_for_p in
            Tensor.select pred ~dim:0 ~index:i
  | I(i) -> let (_, _, (_,pred)) = predictions_for_p in
            Tensor.select pred ~dim:0 ~index:i
  | FP(i) -> let ((_,pred),_,_) = predictions_for_p in
            Tensor.select pred ~dim:0 ~index:i
  | FN(i) -> let (_, (_,pred),_) = predictions_for_p in
            Tensor.select pred ~dim:0 ~index:i
  | FI(i) -> let (_, _, (_,pred)) = predictions_for_p in
            Tensor.select pred ~dim:0 ~index:i
  
                  
let get_prediction predictions (p,id) =
  let predictions_for_p = Hashtbl.find predictions p in
   get_prediction_for_atom predictions_for_p id

     
let name_of_weight id i =
  if id=0 && i=0 then "weight"
  else ("weight_"^(string_of_int (i + id)))
let name_of_bias id i =
  if id=0 && i=0 then "bias"
  else ("bias_"^(string_of_int (i + id)))

let datasize d =
  match d with
   List(l) -> List.length l
  | _ -> 1
