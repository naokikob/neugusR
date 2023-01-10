open Torch
open Global
open Util
   
exception FAIL of string
let range =
  let points1 = [(0.,1,0); (1.,1,1)] in
  let points2 = [(0.5, 2,1)] in
  let points3 = [(1./. 3.,3, 1); (2./. 3., 3, 2)] in
  let points4 = [(1./. 4., 4, 1); (3./. 4., 4, 3)] in
  List.sort (fun (x,_,_) (y, _,_) -> Float.compare x y)  (points1@points2@points3@points4)

let abs_sign r =
  if r< 0. then (Float.abs r, false)
  else (r, true)

let rec find_ratio r range =
  match range with
    [] -> []
  | [(_,x,y)] -> [(x,y)]
  | (r1,x1,y1)::(r2,x2,y2)::range' ->
     if r1 <= r && r < r2 then [(x1,y1);(x2,y2)]
     else find_ratio r ((r2,x2,y2)::range')


let rec find_devisor range r =
  match range with
    [] -> 1
  | [_] -> 1
  | (r1,x1,_)::(r2,x2,y2)::range' ->
     if r1 <= r && r < r2 then
       if r -. r1 < r2 -. r then x1
       else x2
     else find_devisor ((r2,x2,y2)::range') r 

    
let rec gcd x y =
  assert (x>=0 && y>=0);
  if x=0 then y
  else if y=0 then x
  else if x>y then gcd (x-y) y
  else gcd x (y-x)

let lcm x y =
  assert (x>0 && y>0);
  x * y / (gcd x y)
  
let normalize (x,y,z) =
  let d = gcd x (gcd y z) in (x/d, y/d, z/d)
let normalize2 (x,y) =
  let d = gcd x y in (x/d, y/d)

(* returns an index with the maximum absolute value *)
let max_index a arity from =
  let index = ref from in
  let maxelem = ref (Float.abs(a.(from))) in
  for i=from+1 to from+arity-1 do
    let x = Float.abs(a.(i)) in
    if x > !maxelem then
      (index := i; maxelem := x)
  done;
  !index

let get_devisor x =
  let r = Float.abs x in find_devisor range r

let lcm_of_array a arity =
  let x = ref 1 in
  (*  let size = Array.length a in *)
  (for i=0 to arity-1 do
    x := lcm !x a.(i)
   done;
   !x)

let fold_constants a arity biases _ =
  let (_,x) = List.fold_left
    (fun (i,c) bias ->
      let y = a.(i) in
      let _ = (a.(i) <- 0.) in
      (i+1, y *. bias +. c))
    (arity, 0.)
    biases
  in
  a.(arity) <- Float.ceil(x)

let to_fraction ((a,b), weight) earity biases =
  let i = max_index a earity 0 in
  let maxelem = a.(i) in
  let a = Array.map (fun x -> x /. maxelem) a in
  let devisors = Array.map get_devisor a in
  let common_divisor = float_of_int(lcm_of_array devisors earity) in
  let flag = (weight>0. && maxelem > 0.) || (weight<0. && maxelem < 0.) in
  let a = Array.map (fun x -> x *. common_divisor) a in
  let _ = if !poly then () else fold_constants a earity biases flag in
  let intarray = Array.map (fun x -> Float.to_int(Float.round x)) a in
  let c = if !poly then Float.to_int(Float.round b)
          else let x = intarray.(earity) in
               (intarray.(earity) <- 0; x)
  in
  let intarray2 = Array.map (fun x -> -x) intarray in
  if !dualqual 
  then
    let errorsp = List.init !qcerror (fun x->x+1) in (* [1;...;!qcerror] *)
    let errors = errorsp@(List.map (fun x-> -x) errorsp) in
    let quals_primary = [(intarray, c, true, 1);(intarray2, -(c-1), true, 1)] in
    let quals_subp = List.map (fun i-> (intarray,c+i,true,0)) errors in
    let quals_subn = List.map (fun i-> (intarray2,-(c-1)+i, true, 0)) errors in
    quals_primary@quals_subp@quals_subn
  (*                               
    [(intarray, c, true, 1); (intarray2, -(c-1), true, 1); (intarray, c+1, true,0);
     (intarray2, -(c-2), true,0); (intarray, c-1, true,0); (intarray2, -c, true, 0)]
   *)
  else if flag then [(intarray, c, true,1)]
  else [(intarray2, -(c-1), true,1)]
                   
let print_candidate (x,y,z) =
    Printf.printf "%d x + %d y + %d, " x y z

(* l0: qualifiers with priority 0, l1: qualifiers with priority 1 *)
let pushone y (l0,l1) =
  let (a,c,f,priority) = y in
  if priority=0 then
    if List.exists (fun (a',c',f',_)-> a=a' && c=c' && f=f') l1
       || List.exists (fun (a',c',f',_)-> a=a' && c=c' && f=f') l0
    then (l0,l1)
    else (y::l0, l1)
  else
    if List.exists (fun (a',c',f',_)-> a=a' && c=c' && f=f') l1 then (l0,l1)
    else (List.filter (fun (a',c',f',_)-> not(a=a' && c=c' && f=f')) l0, y::l1)
  
let rec push x (l1,l2) =
  match x with
    [] -> (l1,l2)
  | y::x' -> push x' (pushone y (l1,l2))

let extract_qualifiers p rvec =
  let max_size = Array.length rvec in
  let cut = min max_size (max !num_of_candidates
                                 (Float.to_int (Float.round (!ratio_extraction *. (Float.of_int !hidden_nodes))))) in
  let indices = List.init cut (fun x->x) in
  (*  let arity = arity_of p p in *)
  let earity = earity_of p in
  let (quals0,quals1) =
    List.fold_left
      (fun ql i ->
        let x = to_fraction (rvec.(i)) earity (Hashtbl.find biastab p)in
        push x ql)
      ([],[])
      indices
  in
  let quals = List.rev_append quals1 (List.rev_append quals0 []) in
    Hashtbl.replace qualtab p quals

let eval_qual p earity args qual =
  let (coeffs, const, flag,_) = qual in
  let c = ref (Float.of_int const) (* constant part *)
  in (* add coeffs * args *)
  let monomials = monomials_of p in
  for j=0 to earity-1 do
    c := !c +. (Float.of_int (coeffs.(j))) *. (value_of_monomial p args monomials j)
  done;
  if flag then !c>0.0 else !c <0.0
(**  
  let j = ref 0 in
  (* j: index for coefficients; j may not equal i in the presence of mod terms *)
  (for i=0 to arity-1 do
    let coeff = Float.of_int (coeffs.(!j)) in
    match List.nth args i with
      Float(x) -> (c := !c +. coeff *. x; j := !j+1)
    | Int(n) -> (c := !c +. coeff *. (Float.of_int n);
                 if !mod2 then
                   (c := !c +. (Float.of_int coeffs.(!j+1)) *. (Float.of_int (absmod n 2));
                    j := !j+2)
                 else j := !j+1
                )
    | Bool(b) ->
       if b then (c := !c +. coeff; j := !j+1)
   done;
   if flag then !c>0.0 else !c <0.0
  )
 **)
  
let eval_atom (p,id) =
  let args = Hashtbl.find id2rawdatatab id in
  let quals = Hashtbl.find qualtab p in
  let earity = earity_of p in
  let dnf = Hashtbl.find predtab p in
  List.exists
    (fun conj ->
      let qc = List.combine quals conj in
      List.for_all
        (fun (qual, b) ->
          not(b) || eval_qual p earity args qual)
        qc)
  dnf
  
let check_imp (nl, pl) =
  List.exists (fun atom -> (not (eval_atom atom))) nl
  || List.exists (fun atom -> (eval_atom atom)) pl

  
(* entry2 has more "true" than entry 1 *)  
let entry_subsumed entry1 entry2 =
  let entry12 = List.combine entry1 entry2 in
  List.for_all (fun (b1,b2) -> b2 || not(b1)) entry12
  
let add_to_ptab entry ptab =
  if List.exists (fun entry' -> entry_subsumed entry' entry) ptab
  then ptab
  else
    let ptab' = List.filter (fun entry' -> not(entry_subsumed entry entry')) ptab in
    entry::ptab'

let add_to_ntab entry ntab =
  if List.exists (fun entry' -> entry_subsumed entry entry') ntab
  then ntab
  else
    let ntab' = List.filter (fun entry' -> not(entry_subsumed entry' entry)) ntab in
    entry::ntab'

let is_imp_atomid atomid =
  match atomid with
    I(_) -> true
  | _ -> false
    
let get_truth_tables p quals ignore_imp =
  let predictions_for_p = Hashtbl.find !last_predictions p in
  let inputs = Hashtbl.find rawdatatab p in
  let earity = earity_of p in
  let (ptab,ntab) =
    Hashtbl.fold
      (fun args atomid (postab, negtab) ->
        let quals_truthtab = List.map (eval_qual p earity args) quals in
        match atomid with
          P(_) -> ((add_to_ptab quals_truthtab postab), negtab)
        | N(_) -> (postab, add_to_ntab quals_truthtab negtab)
        | I(_) ->
           if ignore_imp then (postab, negtab)
           else
             if Tensor.to_float0_exn (get_prediction_for_atom predictions_for_p atomid) > 0.5 then
               ((add_to_ptab quals_truthtab postab), negtab)
             else
               (postab, add_to_ntab quals_truthtab negtab)
        | _ -> raise TODO
      )
      inputs
      ([], [])
  in
  if List.exists (fun conj1 -> List.exists (fun conj2 -> entry_subsumed conj2 conj1) ptab) ntab
  then raise (FAIL "qualifiers missing")
  else (ptab,ntab)

let print_args = Dataloader.output_args stdout
               
let print_boollist l =
  (print_string "["; List.iter (fun b-> if b then print_string "true;" else print_string "false;") l;
   print_string "]")

let print_truthtab p inputs quals labels earity =
      Hashtbl.iter
      (fun args id ->
        let quals_truthtab = List.map (eval_qual p earity args) quals in
          (print_string "data: "; print_args args;
           print_string "qualifier values:"; print_boollist (quals_truthtab@[labels.(id)]);print_string "\n")
      )
      inputs
  
let rec minimize_conj_aux ntab quals conja i priority=
  if i<0
  then ()
  else if conja.(i) && (priority_of_qual quals i = priority) then
    (conja.(i)<- false;
     if List.exists (entry_subsumed (Array.to_list conja)) ntab
     then (conja.(i)<-true; minimize_conj_aux ntab quals conja (i-1) priority)
     else minimize_conj_aux ntab quals conja (i-1) priority
    )
  else minimize_conj_aux ntab quals conja (i-1) priority

let simplify_dnf dnf =
  List.fold_left
    (fun dnf' conj ->
      if List.exists (fun conj' -> entry_subsumed conj' conj) dnf'
      then dnf'
      else
        conj::(List.filter (fun conj' -> not(entry_subsumed conj conj')) dnf')
    )
    []
    dnf
  
let minimize_conj ntab quals conj =
  let conja = Array.of_list conj in
  let n = List.length(conj)-1 in
  (minimize_conj_aux ntab quals conja n 0;
   minimize_conj_aux ntab quals conja n 1;
   Array.to_list conja)
  
let construct_predicate_p p ignore_imp =
  let quals = try Hashtbl.find qualtab p with Not_found -> assert false in
  let (ptab,ntab) = get_truth_tables p quals ignore_imp in
  if ptab=[]
  then (* since there is no positive data, return the formula "false" *)
    []  (* false in DNF *)
  else
    let dnf =
      List.fold_left
        (fun dnf conj ->
          if List.exists (fun conj' -> entry_subsumed conj' conj) dnf
          then dnf
          else
            let conj' = minimize_conj ntab quals conj in
            conj'::(List.filter (fun conj''-> not(entry_subsumed conj' conj'')) dnf)
        )
        []
        ptab
    in dnf
    (*    let dnf = List.map (minimize_conj ntab quals) ptab in 
    simplify_dnf dnf
     *)
  
let construct_predicates() =
 let complete = ref true in
   ( Hashtbl.iter
       (fun p _ -> (* kinds are ignored for the moment; the special treatment would be required for Booleans *)
         let formula =
           if !last_imp_miss=0 then
             try construct_predicate_p p false
             with FAIL _ ->
               (complete := false;
                construct_predicate_p p true)
           else
             (complete := false;
              construct_predicate_p p true)
         in
         Hashtbl.replace predtab p formula
       )
       qualtab;
     if !complete then ()
     else (* check implication constraints *)
       if List.for_all check_imp !implications
       then ()
       else raise (FAIL "failed to find a solution for implication constraints\n")
   )

let output_exp_sub fp monomials coeffs const =
  let print_plus = ref false in
  let arity = List.length monomials in
  for i=0 to arity-1 do
     let s = string_of_monomial (List.nth  monomials i) in
     let k = coeffs.(i) in
     if k=0 then ()
     else
       (if k>0 then
          (if !print_plus then output_string fp " + ";
           if k>1||s="" then Printf.fprintf fp "%d * " k)
        else
          (output_string fp " -";
           if k< -1 then (output_string fp " "; Printf.fprintf fp "%d * "(abs(k))));
        output_string fp s;
        print_plus := true)
   done;
   let k = const in
   if k=0 && !print_plus then ()
   else
     (if k>=0 then if !print_plus then output_string fp " + " else ()
      else output_string fp " - ";
      Printf.fprintf fp "%d" (abs k))
  
let output_exp fp wa monomials =
  let arity = List.length monomials in
  output_exp_sub fp monomials wa wa.(arity)
let print_exp_sub = output_exp_sub stdout
let print_exp = output_exp stdout
  
let print_qual _ monomials (coeffs,const, flag,_) =
  print_exp_sub monomials coeffs const;   
  if flag then print_string " > 0"
  else print_string " < 0"

let rec print_conj_aux p monomials qc op default =
  match qc with
    [] -> print_string default
  | (q,b)::qc'->
     if b then
       (print_string op; print_qual p monomials q; print_conj_aux p monomials qc' " /\\" "")
     else
       print_conj_aux p monomials qc' op default
     
let print_conj p monomials quals conj =
  let qc = List.combine quals conj in
  print_conj_aux p monomials qc "" "true"
  
let rec print_dnf p monomials quals dnf flag =
  match dnf with
    [] -> print_string "false"
  | [conj] ->
     if flag then print_string "(";
     print_conj p monomials quals conj;
     if flag then print_string ")";
  | conj::dnf' ->
     (print_string "(";
      print_conj p monomials quals conj;
      print_string ")\\/";
      print_dnf p monomials quals dnf' true)


let output_log_qual fp1 fp0 p (coeffs,const,flag,priority) =
  let fp = if priority=1 then fp1 else fp0 in
  let earity = earity_of p in
  (for i=0 to earity-1 do
    let c = if flag then coeffs.(i) else -coeffs.(i) in
    output_string fp ((string_of_int c)^", ")
   done;
   let c = if flag then const else -const in
   output_string fp (string_of_int c);
   output_string fp "\n"
  )

  
let print_predicates() =
  Hashtbl.iter
    (fun p dnf ->
      let quals = Hashtbl.find qualtab p in
      let monomials = monomials_of p in
      print_string (p^": ");
      print_dnf p monomials quals dnf false;
      print_string "\n")
    predtab

let print_qualifiers() =
  let (fp1,fp0) =
    match !log_qual with
      Some(file) -> (open_out (file^"1.csv"), open_out (file^"0.csv"))
    | None -> (stdout, stdout) (* dummy *)
  in
 ( Hashtbl.iter
    (fun p quals ->
      let monomials = monomials_of p in
      print_string (p^":\n");
      if not(!log_qual=None) then
        (output_string fp1 (p^":\n");output_string fp0 (p^":\n");
         List.iter (fun q -> output_log_qual fp1 fp0 p q) quals
        );
      List.iter (fun q -> (print_qual p monomials q; print_string "\n")) quals;
      print_string "\n")
    qualtab;
   if not(!log_qual=None) then (close_out fp1; close_out fp0)
 )

let plusarray a a' =
  for i=0 to Array.length(a)-1 do
    a.(i) <- a.(i)+. a'.(i)
  done
  
let rec merge_weights ws =
  match ws with
    [] -> []
  | (ba,wa)::ws' ->
     let (ws1, ws2) = List.partition (fun (ba',_)-> ba=ba') ws' in
     let _ = List.iter (fun (_,wa')-> plusarray wa wa') ws1 in
      (ba,wa)::(merge_weights ws2)           

let rec subsume_ba_aux ba1 ba2 i =
  if i<0 then true
  else
    (ba1.(i) || not(ba2.(i))) && subsume_ba_aux ba1 ba2 (i-1)
  
let subsume_ba ba1 ba2 =
  subsume_ba_aux ba1 ba2 (Array.length(ba1)-1)
  
let rec sum_weights ws =
  match ws with
    [] -> []
  | (ba,wa)::ws' ->
     let ws1 = List.filter (fun (ba',_)-> subsume_ba ba ba') ws' in
     let _ = List.iter (fun (_,wa')-> plusarray wa wa') ws1 in
     (ba,wa)::(sum_weights ws')

let get_qualifier wa biases =
  let n = List.length biases in
  let arity = Array.length wa - n in
  let _ = if n>1 then
            for i=2 to n do
              wa.(arity) <- (List.nth biases i) *. wa.(arity+i-1);
              wa.(arity+i-1) <- 0.0
            done
  in
  let _ = wa.(arity) <- wa.(arity) -. 1.0 in (* adjustment of constant part *)
  let i = max_index wa arity 0 in
  let maxelem = Float.abs(wa.(i)) in
  let wa = Array.map (fun x -> x /. maxelem) wa in
  let devisors = Array.map get_devisor wa in
  let common_divisor = float_of_int(lcm_of_array devisors arity) in
  let wa = Array.map (fun x -> x *. common_divisor) wa in
  let _ = wa.(arity) <- Float.floor(wa.(arity)) in
  let waint = (maxelem, Array.map (fun x -> Float.to_int(Float.round x)) wa) in
  waint

  
  
let print_cond p qa ba ms bms =
  let prefix = ref "" in
  let arity = List.length(ms) in
  let barity = List.length(bms) in
  (
  for i=0 to Array.length ba - 1 do
    if ba.(i) then
      (print_string !prefix;
       prefix := " /\\ ";
       if i < !hidden_nodes then
         let a = qa.(i) in
         print_qual p ms (a, a.(arity), false, 1)
       else if i < !hidden_nodes+barity then
         print_string (string_of_monomial (List.nth bms (i- !hidden_nodes)))
       else
         (print_string "not ";
          print_string (string_of_monomial (List.nth bms (i- !hidden_nodes - barity)))
         )
      )
  done;
  if !prefix="" then print_string "true"
  )

let rec eqarray a1 a2 i n =
  if i>=n then true
  else
    a1.(i)=a2.(i) && eqarray a1 a2 (i+1) n

let cond_imp arity c' c =
  if c=c' then true
  else
    match (c,c') with
      (CondL(q), CondL(q')) ->
       q.(arity) > q'.(arity)
       && eqarray q q' 0 arity
    | _ -> false
  
let rec simplify_cond cond arity scond =
  match cond with
    [] -> scond
  | c::cond' ->
     if List.exists (fun c' -> cond_imp arity c' c) scond
     then simplify_cond cond' arity scond
     else simplify_cond cond' arity (c::(List.filter (fun c' -> not(cond_imp arity c c'))scond))
    
  
let mk_cond qa ba ms bms =
  let barity = List.length(bms) in
  let c = ref [] in
  let qasize = Array.length(qa) in
  (
  for i=Array.length ba - 1 downto 0 do
    if ba.(i) then
      (if i < qasize then
         c := CondL(qa.(i))::!c 
       else if i < qasize+barity then
         c := CondP(i- qasize)::!c
       else
         c := CondN(i- qasize - barity)::!c
      )
  done;
  simplify_cond !c (List.length ms) []
  )
  
let print_case p qa ba wa monomials bmonomials =
  print_cond p qa ba monomials bmonomials;
  print_string " => ";
  print_exp wa monomials

let mk_condclause qa ba wa ms bmonomials =
  let c = mk_cond qa ba ms bmonomials in
  let e = wa in
    (c, e)
  
let print_function p qa w12int monomials bmonomials =
  let _ = print_string ("Function "^p^":\n  ") in
  List.iter
    (fun (ba, wa) ->
      print_case p qa ba wa monomials bmonomials;
      print_string "\n  ")
    w12int


let register_function p qa w12int ms bmonomials =
  let clauses =
    List.map
    (fun (ba, wa) ->
      mk_condclause qa ba wa ms bmonomials)
    w12int
  in
  Hashtbl.replace functab p clauses

let register_recfunction p qa w123 bias ms bms =
  let hivars = List.init !hidden_rnn (fun x->x) in
  let hbvars = List.init !hidden_brnn (fun x->x) in
  let arity = List.length ms in
  let barity = List.length bms in
  let ms' = ms @ (List.map (fun i-> Var(i+arity)) hivars) in
  let bms' = bms @ (List.map (fun i-> Var(i+barity)) hbvars) in
  let clauses =
    List.map
    (fun (ba, (exps, bexps)) ->
      (mk_cond qa ba ms' bms', exps, bexps))
    w123
  in
  Hashtbl.replace recfunctab p (clauses, bias)
  
  
let rec get_eq_qualifiers arity qa j n a (i,w) l =
  if j>=n then (i, l)
  else
    let (w',a') = qa.(j) in
    if eqarray a a' 0 arity then
      if w>w' && w'<0.1 (* w' is unreliable *)then
        get_eq_qualifiers arity qa (j+1) n a (i,w) (j::l)
      else if w < 0.1 (* w is unreliable *) then
        get_eq_qualifiers arity qa (j+1) n a (j,w') (i::l)
      else
        get_eq_qualifiers arity qa (j+1) n a (i,w) l
    else
        get_eq_qualifiers arity qa (j+1) n a (i,w) l
      
let merge_qualifiers qa arity =
  let n = Array.length qa in
  let m = Array.make n None in
  for i=0 to n-1 do
    match m.(i) with
      None ->
       let (w,a) = qa.(i) in
       let (j,l) = get_eq_qualifiers arity qa (i+1) n a (i,w) [] in
       if l=[] then ()
       else
         List.iter (fun k-> m.(k) <- Some(j)) l
    | _ -> ()
  done;
  (Array.map (fun (_,a)->a) qa, m)

let collapse_ba m a =
  let n = Array.length m in
  for i=0 to n-1 do
    match m.(i) with
      None -> ()
    | Some(j) ->
       if a.(i) then
         (a.(i) <- false;
          a.(j) <- true)
  done;
  a

let output_bexp fp be monomials bmonomials =
  match be with
    CondL(e) -> (output_exp fp e monomials; output_string fp " > 0")
  | CondP(i) -> let m = List.nth bmonomials i in
                output_string fp (string_of_monomial m)
  | CondN(i) -> let m = List.nth bmonomials i in
                output_string fp ("not("^(string_of_monomial m)^")")

let print_bexp = output_bexp stdout
               
let neg_qual qual =
  let qual' = Array.map (fun x-> - x) qual in
  let i = Array.length qual' in
  qual'.(i-1) <- qual'.(i-1)+1;
  qual'
                
let bexp_neg be =
  match be with
    CondL(e) -> CondL(neg_qual e)
  | CondP(i) -> CondN(i)
  | CondN(i) -> CondP(i)
                
let print_cond cond monomials bmonomials =
  let prefix = ref "" in
  List.iter
    (fun be ->
      print_string !prefix;
      print_bexp be monomials bmonomials;
      prefix := " /\\ "
    )
    cond;
  if !prefix="" then print_string "true"
  
let print_clause (cond,exp) monomials bmonomials =
  print_cond cond monomials bmonomials;
  print_string " => ";
  print_exp exp monomials


let rec simplify_dtree dt =
  match dt with
    DTbr(c, dt1, dt2) ->
     let dt1'=simplify_dtree dt1 in
     let dt2'=simplify_dtree dt2 in
     if dt1'=dt2' then dt1'
     else DTbr(c, dt1',dt2')
  | _ -> dt
                                                   
let rec output_dtree fp dt monos bmonos =
  match dt with
    DTbr(c, DTtrue, DTfalse) ->
    (output_bexp fp c monos bmonos)
  | 
    DTbr(_, DTtrue, DTtrue) ->
     output_dtree fp DTtrue monos bmonos
  |  DTbr(_, DTfalse, DTfalse) ->
         output_dtree fp DTfalse monos bmonos
  |  DTbr(c, DTfalse, DTtrue) ->
     (output_bexp fp (bexp_neg c) monos bmonos)
  | 
    DTbr(c, dt1, DTfalse) ->
    (output_bexp fp c monos bmonos;
     output_string fp "&&(";
     output_dtree fp dt1 monos bmonos;
     output_string fp ")")
  | 
    DTbr(c, dt1, DTtrue) ->
    (output_bexp fp c monos bmonos;
     output_string fp "||(";
     output_dtree fp dt1 monos bmonos;
     output_string fp ") && ";
     output_bexp fp (bexp_neg c) monos bmonos
    )
  | 
    DTbr(c, DTtrue, dt2) ->
    (output_bexp fp c monos bmonos;
     output_string fp " || ";
     output_bexp fp (bexp_neg c) monos bmonos;
     output_string fp "&&(";
     output_dtree fp dt2 monos bmonos;
     output_string fp ")")
  | 
    DTbr(c, DTfalse, dt2) ->
    (output_bexp fp (bexp_neg c) monos bmonos;
     output_string fp "&&(";
     output_dtree fp dt2 monos bmonos;
     output_string fp ")")
  | 
    DTbr(c, dt1, dt2) ->
    (output_bexp fp c monos bmonos;
     output_string fp "&&(";
     output_dtree fp dt1 monos bmonos;
     output_string fp ") || ";
     output_bexp fp (bexp_neg c) monos bmonos;
     output_string fp "&&(";
     output_dtree fp dt2 monos bmonos;
     output_string fp ")")
  | DTtrue -> output_string fp "true"
  | DTfalse -> output_string fp "false"
    
let print_dtree = output_dtree stdout
                
let print_function_p p monomials bmonomials =
  let clauses = Hashtbl.find functab p in
  print_string ("Function "^p^":\n");
  List.iter (fun c -> (print_string "  ";
                       print_clause c monomials bmonomials;
                       print_string "\n")
    ) clauses

let print_reccase (cond, exps, bexps) ms bms =
  print_cond cond ms bms;
  print_string "==> (\n";
  Array.iter (fun exp -> print_exp exp ms; print_string ",\n  ") exps;
  Array.iter (fun b -> print_string ((string_of_bool b)^",\n  ")) bexps;
  print_string ")\n"
  
let print_recfunction_f p ms bms =
  let (clauses, bias) = Hashtbl.find recfunctab p in
  print_string ("Function "^p^":\n");
  let hivars = List.init !hidden_rnn (fun x->x) in
  let hbvars = List.init !hidden_brnn (fun x->x) in
  (*
  let arity = List.length ms in
  let barity = List.length bms in
   *)
  let warity = arity_of p - 1 in (* -1 is for disregarding the return value *)
  let args = List.init warity (fun x -> x) in
  let ms' = (List.map (fun i-> Var(i+warity)) hivars)@ms in
  let bms' = (List.map (fun i-> Var(i+warity+ !hidden_rnn)) hbvars)@bms in
  Printf.printf "%d + fst (List.fold (fun (" bias;
  List.iter (fun i -> Printf.printf "x%d, " (i+warity)) hivars;
  List.iter (fun i -> Printf.printf "x%d, " (i+warity+ !hidden_rnn)) hbvars;
  print_string ") (";
  List.iter (fun i -> Printf.printf "x%d, " i) args;
  print_string ") -> \n ";
  List.iter (fun c -> print_reccase c ms' bms'; print_string "\n  ") clauses;
  print_string ")\n (";
  List.iter (fun _ -> Printf.printf "0, ") hivars;
  List.iter (fun _ -> Printf.printf "false, ") hbvars;
  print_string " ))\n"
  
let output_recfunction_p fp p ms bms =
  let (bexparray, cexparray) = Hashtbl.find recpredtab p in
  let arity = arity_of p in
  let (kinds,_,_,_) = Hashtbl.find signatures p in
  let hbvars = List.init !hidden_brnn (fun x->x) in
  let hivars = List.init !hidden_rnn (fun x->x) in
  let args = List.init arity (fun i -> i) in
  let listargs = List.map fst
                   (List.filter
                      (fun (_,k) -> k=LIST)
                      (List.combine args kinds))
  in
  let larity = List.length listargs in
  let ms = (List.map (fun i->Var(-i-1)) hivars)@ms in
  let bms = (List.init !hidden_nodes (fun i -> Var(-1001-i)))@
              (List.map (fun i->Var(-i-101)) hbvars)@bms in
  let _ =
    Printf.fprintf fp "let %s " p;
    for i=0 to arity-1 do
      output_string fp (string_of_monomial (Var(i)));
      output_string fp " "
    done;
    output_string fp "= \n  ";
    Printf.fprintf fp "let hd0 x = match x with [] -> -1 | _ -> List.hd x in\n  ";
    Printf.fprintf fp "let tl0 x = match x with [] -> [] | _ -> List.tl x in\n  ";
    Printf.fprintf fp "let rec %s_aux " p;
    List.iter (fun i->
        Printf.fprintf fp "br%d " i)
      hbvars;
    List.iter (fun i->
        Printf.fprintf fp "r%d " i)
      hivars;
    for i=0 to arity-1 do
      output_string fp (string_of_monomial (Var(i)));
      output_string fp " "
    done;
    output_string fp "= \n    match ";
    if larity>1 then     output_string fp "(";
    for i=0 to larity-1 do
      output_string fp (string_of_monomial (Var (List.nth listargs i)));
      if i<larity-1 then output_string fp ", "
    done;
    if larity>1 then     output_string fp ")";
    output_string fp " with\n      ";
    if larity>1 then     output_string fp "(";
    for i=0 to larity-1 do
      output_string fp "[]";
      if i<larity-1 then output_string fp ", "
    done;
    if larity>1 then output_string fp ")";
    output_string fp " -> br0\n     | _ -> \n        ";
    List.iter (fun larg ->
        Printf.fprintf fp "let x%d' = tl0 x%d in\n        " larg larg;
        Printf.fprintf fp "let x%d = hd0 x%d in\n        " larg larg)
      listargs;
    for i=0 to !hidden_brnn-1 do
      Printf.fprintf fp "let br%d' = " i;
      output_dtree fp bexparray.(i) ms bms;
      output_string fp " in\n        "
    done;
    for i=0 to !hidden_rnn-1 do
      Printf.fprintf fp "let r%d' = " i;
      let (dt, coeffs) = cexparray.(i) in
      output_string fp "if ";
      output_dtree fp dt ms bms;
      output_string fp " then ";
      output_exp fp coeffs ms;
      output_string fp " else 0 in\n        ";
    done;
    Printf.fprintf fp "%s_aux " p;
    List.iter (fun i->
        Printf.fprintf fp "br%d' " i)
      hbvars;
    List.iter (fun i->
        Printf.fprintf fp "r%d' " i)
      hivars;
    List.iter (fun i->
     if List.nth kinds i = LIST then
       Printf.fprintf fp "x%d' " i
     else 
       Printf.fprintf fp "x%d " i)
      args;
    Printf.fprintf fp "\nin %s_aux " p;
    List.iter (fun _ ->
        Printf.fprintf fp "true ")
      hbvars;
    List.iter (fun _ ->
        Printf.fprintf fp "0 ")
      hivars;
    List.iter (fun i ->
      Printf.fprintf fp "x%d " i)
      args;
    output_string fp "\n"
  in ()    
    
(*    print_string "fold_left\n  (fun (";
    List.iter (fun i->
        Printf.printf "br%d, " i)
      hbvars;
    List.iter (fun i->
        Printf.printf "r%d" i;
        if i< !hidden_rnn-1 then print_string ", ")
      hivars;
    print_string ") (";
    for i=0 to arity-1 do
      print_string (string_of_monomial (Var(i)));
      if i<arity-1 then print_string ", "
    done;
    print_string ") -> \n    (";
    for i=0 to !hidden_brnn-1 do
      print_dtree bexparray.(i) ms bms;
      print_string ",\n     "
    done;
    for i=0 to !hidden_rnn-1 do
      let (dt, coeffs) = cexparray.(i) in
      print_string "if ";
      print_dtree dt ms bms;
      print_string "\n    then ";
      print_exp coeffs ms;
      print_string "\n    else 0";
      if i< !hidden_rnn-1 then
        print_string ",\n     "
      else  print_string "\n    )\n  )\n (";
    done;
      (* initial values *)
    for i=0 to !hidden_brnn-1 do
      let _ = i in
      print_string "true, "
    done;
    for i=0 to !hidden_rnn-2 do
      let _ = i in
      print_string "0, "
    done;
    print_string "0)\n  normalized_inputs\n";
  in ()
 *)    

let print_recfunction_p = output_recfunction_p stdout 

let output_functions fp =
  Hashtbl.iter
    (fun p (kinds, func, monomials, bmonomials) ->
      if func then
        if is_rnn_kind kinds then
          ()
        else
          ()
      else if is_rnn_kind kinds then
          output_recfunction_p fp p monomials bmonomials
    )
  signatures
                        
let print_functions () =
  Hashtbl.iter
    (fun p (kinds, func, monomials, bmonomials) ->
      if func then
        if is_rnn_kind kinds then
          print_recfunction_f p  monomials bmonomials
        else
          print_function_p p monomials bmonomials
      else if is_rnn_kind kinds then
          print_recfunction_p p  monomials bmonomials
    )
  signatures

let get_intarg i args ms =
  let m = List.nth ms i in
  match m with
    Var(vid) ->
    (match List.nth args vid with
       Int(n) -> n
     | List([]) -> -1
     | List(x::_) -> x
     | _ -> assert false
    )
  | _ -> assert false
  
let eval_qual2 qual hienv ms args =
  let n = Array.length qual in
  let _ = assert(n = !hidden_rnn + List.length(ms) + 1) in
  let sum = ref (qual.(n-1)) in
  for i=0 to !hidden_rnn-1 do
    sum := !sum + qual.(i) * hienv.(i)
  done;
  for i= !hidden_rnn to n-2 do
    sum := !sum + qual.(i) * (get_intarg (i- !hidden_rnn) args ms)
  done;
  !sum
  
let rec eval_condexp cond hbenv hienv ms bms args =
  match cond with
    CondL(qual) ->
     let x = eval_qual2 qual hienv ms args in x>0
  | CondP(i) ->
     let i' = i - !hidden_nodes in
     if i'< !hidden_brnn then
       hbenv.(i')
     else
       let bm = List.nth bms (i'- !hidden_brnn) in
      ( match bm with
         Var(vid) ->
         (match List.nth args vid with
            Bool(b) -> b
          | _ -> assert false (* type error *)
         )
       | Mod2(vid) ->
          let x = 
            match List.nth args vid with
              Int(n) -> n
            | List([]) -> -1
            | List(n::_) -> n
            | _ -> assert false
          in x mod 2 = 0
       | _ -> assert false
      )
  | CondN(i) ->
     not(eval_condexp (CondP(i)) hbenv hienv ms bms args)
    
let rec eval_dtree dt hbenv hienv ms bms args =
  match dt with
    DTtrue -> true
  | DTfalse -> false
  | DTbr(cond,dt1,dt2) ->
     if eval_condexp cond hbenv hienv ms bms args then
       eval_dtree dt1 hbenv hienv ms bms args
     else
       eval_dtree dt2 hbenv hienv ms bms args

let eval_cexp2 (dt,qual)  hbenv hienv ms bms args =
  if eval_dtree dt hbenv hienv ms bms args then
    eval_qual2 qual hienv ms args
  else 0

let next_data d =
  match d with
    List([]) -> List([])
  | List(_::l) -> List(l)
  | _ -> d
  
let eval_recp_step (bexparray, cexparray) hbenv hienv ms bms args =
  let hbenv' = Array.map (fun dt -> eval_dtree dt hbenv hienv ms bms args) bexparray in
  let hienv' = Array.map (fun cexp -> eval_cexp2 cexp hbenv hienv ms bms args) cexparray in
  let args' = List.map next_data args in
  (hbenv', hienv', args')

let show_hbenv hbenv' =
  Array.iter (fun b -> if b then print_string "true " else print_string "false ") hbenv'
let show_hienv hienv' =
  Array.iter (fun i -> Printf.printf "%d " i) hienv'
  
  
let rec eval_recp n (bexparray,cexparray) hbenv hienv ms bms args =
  if n=0 then hbenv.(0)
  else
    let (hbenv', hienv', args') = eval_recp_step (bexparray, cexparray) hbenv hienv ms bms args in
(* 
    let _ = show_hbenv hbenv' in
    let _ = show_hienv hienv'; print_string "\n" in
 *)
    eval_recp (n-1) (bexparray, cexparray) hbenv' hienv' ms bms args'
  
  
let eval_func p args = 
  let (kinds,func,ms,bms) = Hashtbl.find signatures p in
  if func then assert false
  else if is_rnn_kind kinds then
    let (bexparray, cexparray) = Hashtbl.find recpredtab p in
    let hbenv = Array.init !hidden_brnn (fun _-> true) in
    let hienv = Array.init !hidden_rnn (fun _ -> 0) in
    let n = List.fold_left (fun x d -> max x (datasize d)) 0 args in
    eval_recp n (bexparray, cexparray) hbenv hienv ms bms args
  else assert false

let eval_imp nl pl =
  List.exists (fun (p,args) -> not(eval_func p args)) nl
  || List.exists (fun (p,args) -> eval_func p args) pl
  
let check_functions () =
  let error = ref 0 in
  List.iter
    (fun (p, args) ->
      if eval_func p args then ()
      else 
        (print_string "Error for: ";
         print_args args;
         error := !error + 1)
    )
    !posc;
  List.iter
    (fun (p, args) ->
      if eval_func p args then 
        (print_string "Error for: ";
         print_args args;
         error := !error + 1)
      else ()
    )
    !negc;
  List.iter
    (fun (nl,pl) ->
      if eval_imp nl pl then ()
      else
        (print_string "Error for: ";
         Dataloader.output_impc stdout (nl,pl))
    )
    !impc;
  !error = 0
      
  
let or_ba ba1 ba2 =
  let ba = Array.copy ba1 in
  for i=Array.length ba-1 downto 0 do
    ba.(i) <- ba.(i) || ba2.(i)
  done;
  ba

let plus_wa wa1 wa2 =
  let wa = Array.copy wa1 in
  for i=Array.length wa - 1 downto 0 do
    wa.(i) <- wa.(i) +. wa2.(i)
  done;
  wa

let plus_waa waa1 waa2 =
  let waa = Array.copy waa1 in
  for i=Array.length waa1 - 1 downto 0 do
    waa.(i) <- plus_wa waa1.(i) waa2.(i)
  done;
  waa
  
let rec merge_ba_wa ba_wa_list default =
  match ba_wa_list with
    [] -> default
  | [(ba,wa)] -> (Array.copy ba, Array.copy wa)
  | (ba,wa)::ba_wa_list' ->
     let (ba',wa') = merge_ba_wa ba_wa_list' default in
     (or_ba ba ba', plus_wa wa wa')
  
let merge_clause ba_wa_list flags =
  let l = List.combine ba_wa_list flags in
  let ba_wa_list' = List.map fst (List.filter snd l) in
  let default = let ba = Array.make (Array.length (fst (List.hd ba_wa_list))) false in
                let wa = Array.make (Array.length (snd (List.hd ba_wa_list))) 0. in
                (ba, wa)
  in merge_ba_wa ba_wa_list' default

let merge_boolarray num_bvars wb flags =
  let l = List.combine wb flags in
  let wb' = List.map fst (List.filter snd l) in
  let default = Array.make num_bvars false in
  List.fold_left or_ba default wb'

let merge_cexps outdim num_ivars wl flags =
  let l = List.combine wl flags in
  let wl' = List.map fst (List.filter snd l) in
  let default = Array.make outdim (Array.make num_ivars 0.) in
  List.fold_left plus_waa default wl'
  
let merge_bools boutdim bl flags =
  let l = List.combine bl flags in
  let bl' = List.map fst (List.filter snd l) in
  let default = Array.make boutdim false in
  List.fold_left or_ba default bl'
  
let get_classifications p =
  let cls = Hashtbl.find last_classifications p in
  let ca = Array.to_list
             (Array.map
                (fun a-> Array.to_list (Array.map (fun x-> if x>0.5 then true else false) a))
                (Tensor.to_float2_exn cls))
  in
  let cls = List.sort_uniq (fun x y -> compare y x) ca in
    cls 

let get_classifications_for_rnn p =
  let ex = Hashtbl.find last_cexp_examples p in
  let bl = List.map (fun (_,_,x,_,_) -> x ) ex in
  let ca = List.map
              (List.map (fun x-> if x>0.5 then true else false))
           bl
  in
  let cls = List.sort_uniq (fun x y -> compare y x) ca in
    cls 
  
let print_classifications cls =
  List.iter
    (fun ba ->
      List.iter (fun b -> if b then print_string "true;" else print_string "false;") ba;
      print_string "\n")
    cls

  
let construct_function_f p monomials bmonomials =
  let id = id_of_pred p in
  let wn0 = name_of_weight id 0 in
  let wn1 = name_of_weight id 1 in
  let wn2 = name_of_weight id 2 in
  let v = Var_store.all_vars !global_vs in
  let t0 = List.assoc wn0 v in
  let t1 = List.assoc wn1 v in
  let t2 = List.assoc wn2 v in
  let w0 = Tensor.to_float2_exn t0 in
  let w1 = Tensor.to_float2_exn t1 in
  let w2 = Tensor.to_float2_exn t2 in
  let biases = Hashtbl.find biastab p in
  let qa = Array.map (fun wa -> get_qualifier wa biases) w0 in
  let (qa, m) = merge_qualifiers qa (List.length monomials) in
  let cls = get_classifications p in
  (*
  let _ = print_classifications cls in 
   *)
  let wb1 = Array.map
              (fun a ->
                collapse_ba m (Array.map (fun x-> if x> 2.0 then true else false) a))
              w1
  in
  let w12 = List.combine (Array.to_list wb1) (Array.to_list w2) in
  let w12'' = List.map (merge_clause w12) cls in
(*  
  let w12' = merge_weights w12 in
  let w12' = List.sort (fun (wb1,_) (wb2,_) -> compare wb2 wb1) w12' in
  let w12'' = sum_weights w12' in
 *)
  let w12int = List.map
                 (fun (ba,wa) ->
                   let arity = (List.length monomials)+ !hidden_rnn in
                   let n = List.length biases in
                   if n>1 then
                     for i=2 to n do
                       wa.(arity) <- (List.nth biases i) *. wa.(arity+i-1);
                       wa.(arity+i-1) <- 0.0
                     done;
                   (ba, Array.map (fun r -> Float.to_int(Float.round r)) wa)
                 )
                 w12''
  in
  let ba = fst(take_last w12int) in
  let _ = reset_array ba false in 
  (*  let _ = print_string ("#clauses:"^(string_of_int (List.length w12int))) in*)
  register_function p qa w12int monomials bmonomials

  
let construct_recfunction_f p monomials bmonomials =
  let id = id_of_pred p in
  let wn0 = name_of_weight id 0 in  (* for qualifiers; size [hidden1; input+outdim] *)
  let wn1 = name_of_weight id 1 in  (* for nor gates [hidden2; hidden1]*)
  let wn2 = name_of_weight id 2 in  (* for cexp; size [hidden2*outdim;input+outdim ] *)
  let wn3 = name_of_weight id 3 in  (* for boolean hidden states *)
  let wn4 = name_of_weight id 4 in  (* bias for output; dimension 0 *)
  let v = Var_store.all_vars !global_vs in
  let t0 = List.assoc wn0 v in
  let t1 = List.assoc wn1 v in
  let t2 = List.assoc wn2 v in
  let shape = Tensor.size t2 in
  let outdim = !hidden_rnn in
  let boutdim = !hidden_brnn in
  let inputsize = List.hd(List.tl shape) in
  let hidden2 = (List.hd shape)/ (!hidden_rnn) in
  let t2' = Tensor.transpose
                  (Tensor.reshape t2 ~shape:[outdim; hidden2; inputsize]) ~dim0:0 ~dim1:1 in
  let t3 = List.assoc wn3 v in
  let t3' = Tensor.transpose
              (Tensor.reshape t3 ~shape:[boutdim; hidden2])
              ~dim0:0 ~dim1:1 in
  let t4 = List.assoc wn4 v in
  let w0 = Tensor.to_float2_exn t0 in
  let w1 = Tensor.to_float2_exn t1 in
  let w2 = Tensor.to_float3_exn t2' in
  let w3 = Tensor.to_float2_exn t3' in
  let w4 = Float.to_int(Float.round(Tensor.to_float0_exn t4)) in
  let biases = Hashtbl.find biastab p in
  let qa = Array.map (fun wa -> get_qualifier wa biases) w0 in
  let (qa, m) = merge_qualifiers qa (List.length monomials) in
  (* m: map used to merge qualifiers of m.(i)= Some(j) means i should be merged to j *)
  let wb1 = Array.to_list
              (Array.map
              (fun a ->
                collapse_ba m (Array.map (fun x-> if x> 2.0 then true else false) a))
              w1)
  in
  let cls = get_classifications_for_rnn p in
  (* cls is a list of boolean lists whose length is the number of conjuncts;
     It shows which combination of conjuncts is possible 
   *)
  let num_bvars = Array.length (List.hd wb1) in
  let num_ivars = Array.length w2.(0).(0) in
  let wb1' = List.map (merge_boolarray num_bvars wb1) cls in
  let w2' = List.map (merge_cexps outdim num_ivars (Array.to_list w2)) cls in
  let w3b = Array.to_list
              (Array.map (fun a ->
                   Array.map (fun x -> if x>2.0 then true else false) a) w3) in
  let w3b' = List.map (merge_bools boutdim w3b) cls in
  let w2int = (* approximate linear expressions by those with integer coefficients *)
              List.map
                 (fun w2el ->
                   Array.map
                     (fun wa ->
                       let arity = List.length monomials in
                       let n = List.length biases in
                       if n>1 then
                         for i=2 to n do
                           wa.(arity) <- (List.nth biases i) *. wa.(arity+i-1);
                           wa.(arity+i-1) <- 0.0
                         done;
                       Array.map (fun r -> Float.to_int(Float.round r)) wa
                     )
                     w2el)
                 w2'
  in
  (* set the last condition to "true" (= [false;...;false])
     to make conditional expressions exhaustive
   *)
  let _ =
      let ba = take_last wb1' in
      reset_array ba false
  in
  (* for debug
  let _ = print_string "wb1':\n";
          List.iter (fun ba ->
              print_string "[";
              Array.iter (fun b -> print_string ((string_of_bool b)^";")) ba;
              print_string "]\n") wb1'
  in
   *)
  let w123 = (* list of (conditions, cexps, bexps) *)
    List.combine wb1' (List.combine w2int w3b')
  in
  register_recfunction p qa w123 w4 monomials bmonomials


let weight2coeff wa2i rnnnodes monomials scale =
  let arity = List.length monomials in
  let wa2sub = Array.init (Array.length wa2i - rnnnodes) (fun i -> wa2i.(i+rnnnodes)) in
  let i = max_index wa2sub arity 0 in
  let const = wa2sub.(arity) in (* this should be updated if there are more than one bias *)
  if 4.0 *. Float.abs(wa2sub.(i)) < Float.abs(const) (* ad hoc condition *)
  then 
    let const' = Float.round const in
    let ratio = const' /. const in
    let coeffs = Array.init (Array.length wa2i)
                   (fun i -> if i < rnnnodes then Float.to_int(Float.round (wa2i.(i) *. scale))
                             else  Float.to_int(Float.round (wa2i.(i) *. ratio)))
    in
(*    
    let coeffs = Array.map (fun x -> Float.to_int(Float.round (x *. ratio))) wa2i in
 *)
     (ratio /. ((scale+. 1.)/. 2.), coeffs)
  else
    let maxelem = wa2sub.(i) in
    let a = Array.map (fun x -> x /. Float.abs(maxelem)) wa2sub in
    let devisors = Array.map get_devisor a in
    let common_divisor = float_of_int(lcm_of_array devisors arity)
                                     (* better to replace with max? *)
    in
    (*    let a = Array.map (fun x -> x /. Float.abs(maxelem) *. common_divisor) wa2i in *)
    let a = Array.init (Array.length wa2i)
              (fun i -> if i < rnnnodes then wa2i.(i) *. scale
                        else wa2i.(i) /. Float.abs(maxelem) *. common_divisor)
    in
    let coeffs = Array.map (fun x -> Float.to_int(Float.round x)) a in
    let ratio = Float.of_int (coeffs.(i+rnnnodes)) /. maxelem in
      (* to determine the ratio, we take into consideration of the factor
         computed by the first boolean layer *)
      (ratio /. ((scale+. 1.)/. 2.), coeffs)


let get_qualifier2 arity wa =
  let i = max_index wa arity 0 in
  let const =
    let c = wa.(arity) in (wa.(arity) <- 0.; c)
  in
  let maxelem = wa.(i) in
  let wa = Array.map (fun x -> x /. Float.abs(maxelem)) wa in
  let devisors = Array.map get_devisor wa in
  let common_divisor = float_of_int(lcm_of_array devisors arity) in
  (wa.(arity) <- const /. Float.abs(maxelem);
   let wa = Array.map (fun x -> x *. common_divisor) wa in
   let _ = wa.(arity) <- Float.floor(wa.(arity)) in
   let waint = Array.map (fun x -> Float.to_int(Float.round x)) wa in
   waint
  )   

let eval_linexp qual ins =
  let arity = List.length ins in
  let _ = if not(Array.length qual = arity) then
            (Printf.printf "qualifier dim: %d, ariy: %d\n" (Array.length qual) arity;
             assert false)
  in
  let r = ref 0. in
  for i=0 to arity-1 do
    r := !r +.
           (Float.of_int(qual.(i)) *. (Float.round (List.nth ins i)))
             (* we round the element of each instance to the nearest integer *)
  done;
  !r

let eval_rawlinexp qual ins =
  let arity = List.length ins in
  let _ = if not(Array.length qual = arity) then
            (Printf.printf "qualifier dim: %d, ariy: %d\n" (Array.length qual) arity;
             assert false)
  in
  let r = ref 0. in
  for i=0 to arity-1 do
    r := !r +.
           (Float.of_int(qual.(i)) *. (List.nth ins i))
             (* we round the element of each instance to the nearest integer *)
  done;
  !r
  
let report_classification l1 l2 =
    (print_string "Current classification for \n Positive examples:\n";
     List.iter
       (fun (inp, binp) ->
         print_floatlist inp;
         print_floatlist binp;
         print_string "\n")
       l1;
     print_string "Negative examples:\n";
     List.iter
       (fun (inp, binp) ->
         print_floatlist inp;
         print_floatlist binp;
         print_string "\n")
       l2)

let entropy (x, y) =
  if x=0 || y=0 then 0.
  else
    let p = Float.of_int x /. Float.of_int (x+y) in
    -. p *. log p -. (1. -. p) *. log (1. -. p)

let aventropy (x1,y1) (x2,y2) =
  let d1 = Float.of_int(x1+y1) in
  let d2 = Float.of_int(x2+y2) in
  let e1 = entropy (x1,y1) in
  let e2 = entropy (x2,y2) in
     (d1 *. e1 +. d2 *. e2 ) /. (d1 +. d2)
    
let rec classify wsorted quals pos neg =
  if neg=[] then DTtrue
  else if pos=[] then DTfalse
  else
    match wsorted with
      [] ->
       (print_string "Warning: failed to classify\n";
        report_classification pos neg;
       if List.length pos > List.length neg then DTtrue else DTfalse)
    | 
      (w,i)::wsorted' ->
       (*
       report_classification pos neg;
       Printf.printf "Using %d for classification" i;
        *)
       if i < Array.length quals then (* use qualifier for classification *)
         let qual = quals.(i) in
         let arity = Array.length qual in
         let qual' = if w>0. then Array.map (fun x->x) qual
                     else neg_qual qual in
         let vpos = List.map (fun (ins,_)-> eval_linexp qual' ins) pos in
         let vneg = List.map (fun (ins,_)-> eval_linexp qual' ins) neg in
         (* adjust the constant part by +-1 *)
         let vpos1 = List.filter (fun x-> x<=1.) vpos in
         let vneg1 = List.filter (fun x-> x<=1.) vneg in
         let vpos2 = List.filter (fun x-> x<=0.) vpos1 in
         let vneg2 = List.filter (fun x-> x<=0.) vneg1 in
         let vpos3 = List.filter (fun x-> x<= -1.) vpos2 in
         let vneg3 = List.filter (fun x-> x<= -1.) vneg2 in
         let npos = List.length vpos in
         let nneg = List.length vneg in
         let npos1 = List.length vpos1 in
         let nneg1 = List.length vneg1 in
         let npos2 = List.length vpos2 in
         let nneg2 = List.length vneg2 in
         let npos3 = List.length vpos3 in
         let nneg3 = List.length vneg3 in
         let posgt1 = npos - npos1 in
         let neggt1 = nneg - nneg1 in
         let posgt0 = npos - npos2 in
         let neggt0 = nneg - nneg2 in
         let posgt_1 = npos - npos3 in
         let neggt_1 = nneg - nneg3 in
         let entropy1 = aventropy (posgt1, neggt1) (npos - posgt1, nneg - neggt1) in
         let entropy0 = aventropy (posgt0, neggt0) (npos - posgt0, nneg - neggt0) in
         let entropy_1 = aventropy (posgt_1, neggt_1) (npos - posgt_1, nneg - neggt_1) in
         let score0 = (* would be better to use entory *)
           List.length (List.filter (fun x-> x>0. && x<=1.) vpos)
           -  List.length (List.filter (fun x-> x>0. && x<=1.) vneg)
         in
         let score1 =
           List.length (List.filter (fun x-> x> -1. && x<=0.) vpos)
           -  List.length (List.filter (fun x-> x> -1. && x<=0.) vneg)
         in
         let _ =
           Printf.printf "For classifier %d with weight %f:\n" i w;
           Printf.printf "Entropies: %f, %f, %f\n" entropy1 entropy0 entropy_1;
           Printf.printf "scores: %d, %d\n" score0 score1
         in
         (*
         let bias = 
          if score1>0 then -1
          else if score0<0 then 1 else 0 in
          *)
         let bias =
           if !use_entropy then
             if entropy1 < entropy0 then
               if entropy1 < entropy_1 then -1
               else 1
             else
               if entropy_1 < entropy0 then 1
               else 0
           else
             0
         in
         let _ = qual'.(arity-1) <- qual'.(arity-1) - bias in
         let (pos1, pos2) =
           list_filter2 pos (fun (ins,_) -> eval_linexp qual' ins > 0.) in
         let (neg1, neg2) =
           list_filter2 neg (fun (ins,_) -> eval_linexp qual' ins > 0.) in
         if (pos2=[] && neg2=[] || pos1=[] && neg1=[]) then
           (* the predicate was useless *)
           (Printf.printf "qualifier %d was useless\n" i;
           classify wsorted' quals pos neg)
         else
           let dt1 = classify wsorted' quals pos1 neg1 in
           let dt2 = classify wsorted' quals pos2 neg2 in
           DTbr(CondL(qual'), dt1, dt2)
       else
         let j = i (* - Array.length quals *) in (* index of the classifying boolean input *)
         let flag = if w > 0. then 1.0 else -1. in
         let pos1 =
           List.filter 
             (fun (_,bns) -> (List.nth bns j) *. flag > !bool_threshold)
             pos
         in
         let pos2 =
           List.filter 
             (fun (_,bns) -> (List.nth bns j) *. flag < -. !bool_threshold)
             pos
         in
         (*
         let (pos1,pos2) =
           list_filter2 pos (fun (_,bns) -> (List.nth bns j) *. flag > !bool_threshold)
         in
          *)
         let neg1 =
           List.filter 
             (fun (_,bns) -> (List.nth bns j) *. flag > !bool_threshold)
             neg
         in
         let neg2 =
           List.filter 
             (fun (_,bns) -> (List.nth bns j) *. flag < -. !bool_threshold)
             neg
         in
         (*
         let (neg1,neg2) =
           list_filter2 neg (fun (_,bns) -> (List.nth bns j) *. flag > !bool_threshold) 
         in
          *)
         if (pos2=[] && neg2=[] || pos1=[] && neg1=[]) then
           (* the predicate was useless *)
           (Printf.printf "qualifier %d was useless\n" i;
           classify wsorted' quals pos neg)
         else
           let dt1 = classify wsorted' quals pos1 neg1 in
           let dt2 = classify wsorted' quals pos2 neg2 in
           if flag>0. then
             DTbr(CondP(j), dt1, dt2)
           else 
             DTbr(CondN(j), dt1, dt2)

let report_classification_examples l1 l2 =
    (print_string "Finding classification for \n Positive examples:\n";
     List.iter
       (fun (inp, binp, bs, out, bout) ->
         print_floatlist inp;
         print_floatlist binp;
         print_floatlist bs;
         print_floatlist out;
         print_floatlist bout;
         print_string "\n")
       l1;
     print_string "Negative examples:\n";
     List.iter
       (fun (inp, binp, bs, out, bout) ->
         print_floatlist inp;
         print_floatlist binp;
         print_floatlist bs;
         print_floatlist out;
         print_floatlist bout;
         print_string "\n")
       l2)

let adjust_qualifier qual samples =
  let _ = print_string "Adjusting qualifiers\n" in
  let samples' =
    List.map (fun (ins,out) ->
        (eval_rawlinexp qual ins, out)) samples in
  let pos1 = List.filter (fun (_,out) -> out > 0.5) samples' in
  let pos2 = List.filter (fun (_,out) -> out > 0. && out <= 0.5) samples' in
  let neg2 = List.filter (fun (_,out) -> out <= 0. && out >= -0.5) samples' in
  let neg1 = List.filter (fun (_,out) -> out < -0.5) samples' in
  let posmin = List.fold_left (fun x (y,_) -> min x y) 100.0 pos1 in
  let negmax = List.fold_left (fun x (y,_) -> max x y) (-. 100.0) neg1 in
  let posmin2 = List.fold_left (fun x (y,_) -> min x y) posmin pos2 in
  let negmax2 = List.fold_left (fun x (y,_) -> max x y) negmax neg2 in
  let mean =
    if posmin2 > negmax2 then
      Float.to_int(Float.floor ((posmin2  +. negmax2) /. 2.0)) 
    else
      Float.to_int(Float.floor ((posmin  +. negmax) /. 2.0)) in
  let _ = Printf.printf "Posmax1 %f, osmax2 %f, negmax2 %f, negmax 1 %f, adjusting constant by %d\n"
            posmin posmin2 negmax2 negmax mean in
  let i = Array.length qual in
    qual.(i-1) <- qual.(i-1) - mean;
    if posmin <= negmax then
      print_string "warining: coefficients need to be adjusted\n";
    qual
  
  
let adjust_qualifiers quals logs =
  let k = Array.length quals in
  for i=0 to k-1 do
    quals.(i) <-
      adjust_qualifier quals.(i)
        (List.map (fun (ins,bins) -> (ins, List.nth bins i)) logs)
  done;
  quals
  
let construct_recfunction_p p monomials bmonomials =
  let arity = List.length monomials in
  let id = id_of_pred p in
  let bid = bid_of_pred p in
  let wn0 = name_of_weight id 0 in  (* for qualifiers; size [hidden1; out+input] *)
  let wn1 = name_of_weight id 1 in  (* for first-logical gates [hidden2+out; hidden1+bout+binput]*)
  let wn2 = name_of_weight id 2 in  (* for cexp; size [out;input] *)
  let wn3 = name_of_weight id 3 in  (* for second-logical gates [bout; hidden2] *)
  let b1 = name_of_bias bid 0 in
  let b3 = name_of_bias bid 1 in
  let v = Var_store.all_vars !global_vs in
  let wt0 = List.assoc wn0 v in
  let wt1 = List.assoc wn1 v in
  let wt2 = List.assoc wn2 v in
  let wt3 = List.assoc wn3 v in
  let bt1 = List.assoc b1 v in
  let bt3 = List.assoc b3 v in
  let wt1shape = Tensor.shape wt1 in
  let outdim = !hidden_rnn in
  let boutdim = !hidden_brnn in
  let hidden2 = (List.hd wt1shape) - outdim in
  let bdim = List.hd (List.tl wt1shape) in (* hidden1+bout+bin *)
  let wa1 = Tensor.to_float2_exn wt1 in
  let wa2 = Tensor.to_float2_exn wt2 in
  let wa3 = Tensor.to_float2_exn wt3 in
  let logs = Hashtbl.find last_bexp_examples p in
  let bss = List.map (fun (_,_,bs,_,_) -> drop_n hidden2 bs) logs in
  let bmaxs = List.fold_left (fun l1 l2 -> List.map (fun (x, y) -> max x y) (List.combine l1 l2))
                (List.init outdim (fun _-> -0.9)) bss
  in
  let bexparray = Array.init boutdim (fun _ -> DTtrue) in
  let (cexpinfo, cexparray) =
    try
      let cmatrix = Hashtbl.find cmatrixtab p in
      let wa2 = Tensor.to_float2_exn (Tensor.tr cmatrix) in
      let cexpinfo = Array.map (fun a -> (1.0, Array.map Float.to_int a)) wa2 in
      let cexparray = Array.map (fun (_,a) -> (DTtrue, a)) cexpinfo in
      Hashtbl.remove cmatrixtab p;
      (* since this cmatrix has been used before, we infer a new cmatrix for the next trial, to avoid 
         repeated failures due to an inappropriate choice of cmatrix *)
      (cexpinfo, cexparray)
    with
      Not_found ->
      let cexpinfo = (* (scaling_factor, coefficients) *)
        Array.init outdim (fun _ -> (1.0, [||])) in
      let cexparray = Array.init outdim (fun _ -> (DTtrue, [| |])) in
      for i=0 to outdim-1 do
        let wa2i = wa2.(i) in
        (
          cexpinfo.(i) <- weight2coeff wa2i outdim monomials (List.nth bmaxs i);
          let (ratio, coeffs) = cexpinfo.(i) in
          ( Printf.printf("scaling factor: %f, integer coefficients: ") ratio;
            Array.iter (fun c -> print_int c; print_string " ") coeffs;
            print_string "\n";
            cexparray.(i) <- (DTtrue, coeffs)
          )
        )
      done;
      let carray = Array.map (fun (_,a) -> Array.map Float.of_int a) cexpinfo in
      Hashtbl.replace cmatrixtab p (Tensor.tr (Tensor.of_float2 carray));
      (cexpinfo,cexparray)
  in
  (* compute candidate qualifiers for inputs *)
  let wa0 = Tensor.to_float2_exn wt0 in
  for i=0 to Array.length(wa0)-1 do (* rescale the coefficients for the hidden rnn nodes *)
    for j=0 to outdim-1 do
      let (scale, _) = cexpinfo.(j) in
      if scale > 0. then wa0.(i).(j) <- wa0.(i).(j) /. scale
    done
  done;
  (* rescale inputs of logs *)
  let logs' = List.map
                (fun (ins,bins,bs,outs,bouts) ->
                  let l = List.combine ins (List.init (List.length ins) (fun x->x)) in
                  let ins' =
                    List.map (fun (x,i) ->
                        if i<outdim then
                          let (scale,_)=cexpinfo.(i) in
                          x *. scale
                        else
                          x) l
                  in
                  (ins',bins,bs,outs,bouts)) logs
  in
  let quals = Array.map (get_qualifier2 (outdim+arity)) wa0 in
  let monomials_rnodes = List.init outdim (fun i -> Var(-1-i)) in
  let monomials' = monomials_rnodes@monomials in
  let monomials_rbnodes = List.init boutdim (fun i -> Var(-101-i)) in
  let monomials_qnodes = List.init (Array.length quals) (fun i -> Var(-1001-i)) in
  let bmonomials' = monomials_qnodes@monomials_rbnodes@bmonomials in
  let _ =
    print_string "Qualifiers:\n";
    Array.iter
      (fun qual ->
        print_qual () monomials' (qual, qual.(outdim+arity), true,());
        print_string "\n")
      quals
  in
  let quals = adjust_qualifiers quals (List.map (fun (ins,bins,_,_,_)-> (ins,bins)) logs') in
  let _ =
    print_string "Qualifiers:\n";
    Array.iter
      (fun qual ->
        print_qual () monomials' (qual, qual.(outdim+arity), true,());
        print_string "\n")
      quals
  in
  (* infer conditions used in the conditional expressions,
     by looking at the scalar factors in the actualy runs of rnn *)
  for i=0 to outdim-1 do
    let dt =
      (*
      let (l1,l2) =
        list_filter2 logs' (fun (_,_, bs,_,_) ->
            List.nth bs (hidden2+i) > 0.) (* this threshold is ad hoc *)
      in
       *)
      let l1 =
        List.filter  (fun (_,_, bs,_,_) ->
            List.nth bs (hidden2+i) > 0.) logs' (* this threshold is ad hoc *)
      in
      let l2 =
        List.filter (fun (_,_, bs,_,_) ->
            List.nth bs (hidden2+i) < -0.4) logs' (* this threshold is ad hoc *)
      in
      (if l2=[] then DTtrue (* condition true *)
       else if l1=[] then
         (* factor is close to zero; so, the expression should be ignored *)
         DTfalse
       else
         let _ = if !verbose then report_classification_examples l1 l2 in
         let l1' = List.map (fun (ins,bins,_,_,_) -> (ins,bins)) l1 in
         let l2' = List.map (fun (ins,bins,_,_,_) -> (ins,bins)) l2 in
         let w = Array.to_list(wa1.(hidden2+i)) in
         let wsize = List.length w in
         let wsorted = List.sort
                         (fun (x,_) (y,_) -> compare (Float.abs y) (Float.abs x))
                         (List.combine w (List.init wsize (fun i->i)))
         in
         let dt = simplify_dtree (classify wsorted quals l1' l2') in
         dt)
    in
         print_string "Conditions for outs: ";
         print_dtree dt monomials' bmonomials';
         print_string "\n";
         let (_, coeffs) = cexparray.(i) in
         cexparray.(i) <- (dt, coeffs)
  done;
  for i=0 to boutdim-1 do
    (* construct formulas for Boolean outputs *)
    let w3 = wa3.(i) in
    (* compute max/min weights *)
    let wmax = Array.make bdim 0.0 in
    (*    let wmin = Array.make bdim 0.0 in *)
    for j=0 to bdim-1 do
      for k=0 to hidden2-1 do
        let w = wa1.(k).(j) *. w3.(k) in
        if Float.abs(w) > Float.abs(wmax.(j)) then
          wmax.(j) <- w
(*        
        if w> 0. then
          wmax.(j) <- max w wmax.(j)
        else 
          wmin.(j) <- min w wmin.(j)
 *)
      done
    done;
    let wl1 = List.init bdim (fun j -> (wmax.(j), j)) in
    (*    let wl2 = List.init bdim (fun j -> (wmin.(j), j)) in *)
    let wsorted = List.sort
                    (fun (x,_) (y,_) -> compare (Float.abs y) (Float.abs x))
                    wl1
                    (* (wl1@wl2) *)
    in
    (* classify Boolean output *)
    (*
    let (l1,l2) =
        list_filter2 logs' (fun (_,_, _,_,bouts) ->
            List.nth bouts i > 0.) (* this threshold is ad hoc *)
    in
     *)
    let l1 =
        List.filter (fun (_,_, _,_,bouts) ->
            List.nth bouts i > 0.1)  logs' (* this threshold is ad hoc *)
    in
    let l2 =
        List.filter (fun (_,_, _,_,bouts) ->
            List.nth bouts i < -0.1)  logs' (* this threshold is ad hoc *)
    in
    let _ = if !verbose then report_classification_examples l1 l2 in
    let l1' = List.map (fun (ins,bins,_,_,_) -> (ins,bins)) l1 in
    let l2' = List.map (fun (ins,bins,_,_,_) -> (ins,bins)) l2 in
    let dt = simplify_dtree (classify wsorted quals l1' l2') in
    Printf.printf "Conditions for bouts #%d: " i;
    print_dtree dt monomials' bmonomials';
    print_string "\n";
    bexparray.(i) <- dt;
    let dt = classify wsorted [||] l1' l2' in
    Printf.printf "Boolean Conditions for bouts #%d: " i;
    print_dtree (simplify_dtree dt) monomials' bmonomials';
    print_string "\n"
  done;
  let _ = (bt1,bt3) in
  Hashtbl.replace recpredtab p (bexparray, cexparray)

  
let eval_exp e ms args =
  let arity = List.length ms in
  let c = ref (Float.of_int(e.(arity))) in
  for i=0 to arity-1 do
    let x = value_of_monomial "dummy" args ms i in
    c := !c +. (Float.of_int(e.(i)) *.  x)
  done;
  !c

let eval_bexp be ms bms args =
  match be with
    CondL(e) -> eval_exp e ms args < 0.
  | CondP(i) -> value_of_monomial "dummy" args bms i > 0.5
  | CondN(i) -> value_of_monomial "dummy" args bms i < 0.5
     
let eval_cond cond ms bms args =
  List.fold_left
    (fun b be ->
      b && eval_bexp be ms bms args)
    true
    cond
  
let ret_value args =
  match take_last(args) with
    Int(n) -> Float.of_int n
  | Bool(b) -> if b then 1.0 else 0.0
  | Float(x) -> x
  | List(_) -> assert false

let rec add_count d dl =
  match dl with
    [] -> [(d,1)]
  | (d',n)::dl' ->
     if d=d' then (d,n+1)::dl'
     else if d<d' then (d,1)::dl
     else (d',n)::(add_count d dl')

let rec relax_condL ce cond e examples ms bms =
  if examples=[] then (ce, examples)
  else 
  let arity = List.length ms in
  let ce' = Array.copy ce in
  let _ = (ce'.(arity) <- ce.(arity)+1) in
     let (examples1,examples2) = List.partition (eval_cond (CondL(ce')::cond) ms bms) examples in
     if not(examples1=[]) &&
          List.for_all
          (fun args -> Float.abs(ret_value args -. eval_exp e ms args) < 0.1)
          examples1
     then relax_condL ce' cond e examples2 ms bms
     else (ce, examples)
     
let rec relax_cond cond cond1 e examples ms bms =
  match cond with
    [] -> (cond1, examples)
  | c::cond' ->
     let (examples1,examples2) = List.partition (eval_cond (cond'@cond1) ms bms) examples in
     if List.for_all
          (fun args -> Float.abs(ret_value args -. eval_exp e ms args) < 0.1)
          examples1
     then relax_cond cond' cond1 e examples2 ms bms
     else
       match c with
         CondL(e') ->
          let (e'', examples2) = relax_condL e' (cond'@cond1) e examples ms bms in
             relax_cond cond' (CondL(e'')::cond1) e examples2 ms bms
       | _ -> relax_cond cond' (c::cond1) e examples ms bms

let get_margin be ms args =
  match be with
    CondL(e) ->
     let x = Float.to_int(Float.ceil (-. eval_exp e ms args)) in x
  | _ -> assert false

let rec get_minindex m =
  match m with
    [] -> assert false
  | [x] -> (0,x)
  | x::m' ->
     let (i,y)=get_minindex m' in
     if x<=y then (0,x)
     else (i+1,y)
  
let rec merge_margins l =
  match l with
    [] -> assert false
  | [m] -> let (i,x) = get_minindex m in
           List.init (List.length m) (fun j -> if i=j then x else 0)
  | m::l' ->
     let (i,x) = get_minindex m in
     let m' = List.init (List.length m) (fun j -> if i=j then x else 0) in
     let m'' = merge_margins l' in
       List.map (fun (x,y)-> max x y) (List.combine m' m'')

let add_margin cond m arity =
  let l = List.combine cond m in
  List.map
    (fun (be,x) ->
      match be with
        CondL(e) -> let e' = Array.copy e in (e'.(arity) <- e.(arity)+x; CondL(e'))
      | _ -> assert false)
    l
     
let strengthen_cond cond e examples ms bms =
  let (cond1,cond2) = List.partition
                        (function CondL(_) -> true | _ -> false) cond in
  if cond1=[] then
    (* impossible to strengthen *)
    (cond, examples, false)
  else
  let (_,examples2) =
    List.partition (fun args -> Float.abs(ret_value args -. eval_exp e ms args) < 0.1) examples
  in
  let margins2 =
    List.map (fun args -> List.map (fun be -> get_margin be ms args) cond1) examples2 in
  let margin = merge_margins margins2 in
  let cond1' = add_margin cond1 margin (List.length ms) in
  let (examples1',examples2') = List.partition (eval_cond (cond1') ms bms) examples in
  assert(List.for_all 
           (fun args -> Float.abs(ret_value args -. eval_exp e ms args) < 0.1) examples1');
  if examples1'=[] then (* no examples could be matched *)
    ([], examples, false)
  else
    (cond1'@cond2, examples2', true)
  
     
let check_and_amend_clause cond e examples ms bms =
  let arity = List.length ms in
  let (examples1, examples2) = List.partition (eval_cond cond ms bms) examples in
  let diffs =
    List.fold_left
      (fun dl args ->
        let d = (Float.to_int (Float.round (ret_value args -. eval_exp e ms args))) in
        add_count d dl
      )
      []
      examples1
  in
  match diffs with
    [] -> None
  | [(d,_)] -> ((* if d=0 then () else print_string "value amended\n"; *)
                let e' = Array.copy e in
                e'.(arity) <- e.(arity)+d;
(*                print_string "relaxing:\n";
                  print_cond cond ms bms;
 *)
                let (cond',examples2') = relax_cond cond [] e' examples2 ms bms in
                (*
                print_string "==>";
                print_cond cond' ms bms;print_string "\n";
                 *)
                Some(cond', e', examples2'))
  | _ -> (* strengthen conditions *)
     let diffs' = List.sort (fun (_,n1) (_,n2) -> compare n2 n1) diffs in
     let d = fst (List.hd diffs') in
     let e' = Array.copy e in
     e'.(arity) <- e.(arity)+d;
     (*     let e' = Array.copy e in *)
     let (cond', examples1',b) = strengthen_cond cond e' examples1 ms bms in
     let examples2 = examples1'@examples2 in
     if not(b) then
       None
     else
       let (cond'', examples2') = relax_cond cond' [] e' (examples1'@examples2) ms bms in
         Some(cond'', e', examples2')
(*     
     let diffs' = List.sort (fun (_,n1) (_,n2) -> compare n2 n1) diffs in
     let d = fst(List.hd diffs') in
     e.(arity) <- e.(arity)+d;
     let violated = List.filter (fun atomid -> not(eval_exp e ms atomid = 0)) examples1 in
     let cond' = strengthen_cond cond violated ms bms in
     let (_, examples2') = List.partition (eval_cond cond' ms bms) examples in
     (cond', e, examples2')
 *)  
let rec check_and_amend_aux clauses examples ms bms =
  match clauses with
    [] -> (if not(examples=[]) then print_string "Warning: Failed to find an appropriate function\n";
           [])
  | (cond,e)::clauses' ->
     match check_and_amend_clause cond e examples ms bms with
       None ->
        if clauses'=[] then
          if examples=[] then []
          else 
            match check_and_amend_clause [] e examples ms bms with
              None -> check_and_amend_aux clauses' examples ms bms
            | Some(cond',e',_) -> [(cond',e')]
        else check_and_amend_aux clauses' examples ms bms
     | Some(cond',e',examples') ->
     (cond',e')::(check_and_amend_aux clauses' examples' ms bms)

let rec clear_last_cond clauses =
  match clauses with
    [] -> []
  | [(_,e)] -> [([],e)]
  | cl::clauses' -> cl::(clear_last_cond clauses')
       
let check_and_amend_function_p p monomials bmonomials =
  let clauses = Hashtbl.find functab p in
  let pexamples = List.map (fun (_,atomid) -> Hashtbl.find id2rawdatatab atomid)
                    (List.filter (fun (p',_) -> p=p') !positives) in
  (*  let _ = print_int (List.length clauses) in*)
  let clauses' = check_and_amend_aux clauses pexamples monomials bmonomials in
  (*  let _ = print_int (List.length clauses') in*)
  let clauses' = clear_last_cond clauses' in
  (* let _ = print_int (List.length clauses') in*)
   Hashtbl.replace functab p clauses'

let check_and_amend_recfunction_p _ _ _ = () (* p ms bms   TODO *)
  
let construct_functions() =
  Hashtbl.iter
    (fun p (kinds,func,monomials,bmonomials) ->
      if func then
        if is_rnn_kind kinds then
          (construct_recfunction_f p monomials bmonomials;
           check_and_amend_recfunction_p p monomials bmonomials)
        else
          (construct_function_f p monomials bmonomials;
           (*         
         print_string "before check_and_amend\n";
         print_function_p p monomials bmonomials;
         print_string "after check_and_amend\n";
            *)
           check_and_amend_function_p p monomials bmonomials)
      else 
        if is_rnn_kind kinds then
          construct_recfunction_p p monomials bmonomials
        else ()
    )
    signatures;
  print_functions();
  if check_functions() then
    if not(!outfile = "") then
      let fp = open_out !outfile in
      (output_functions fp;
       close_out fp; true)
    else true
  else false
