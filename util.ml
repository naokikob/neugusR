open Torch
let rec drop_last l =
  match l with
    [] -> assert false
  | [_] -> []
  | x::l'-> x::(drop_last l')
let rec take_last l =
  match l with
    [] -> assert false
  | [x] -> x
  | _::l'-> take_last l'

let rec drop_n n l =
  if n=0 then l
  else
  match l with
    [] -> assert false
  | _::l'-> drop_n (n-1) l'

(* l --> (fist_n_elements, rest) *)          
let rec list_partition l n =
  if n<=0 then ([], l)
  else
    match l with
      [] -> ([], [])
    | x::l' ->
       let (l1,l2)=list_partition l' (n-1) in
       (x::l1, l2)
       
let list_filter2 l p =
  (List.filter p l, List.filter (fun x -> not(p x)) l)
       
let reset_array a x =
  for i=Array.length a-1 downto 0 do
    a.(i) <- x
  done
                              
let plus_array a1 a2 =
  for i=Array.length a1-1 downto 0 do
    a1.(i) <- a1.(i)+. a2.(i)
  done

let list_max l =
  List.fold_left (fun m x -> max m x) 0 l

let array_max a =
  Array.fold_left (fun m x -> max m x) 0 a

let string_of_shape l =
 List.fold_left
    (fun s n -> s^(string_of_int(n)^";"))
    ""
    l

let print_darray a =
 ( print_string "[";
  Array.iter (fun b -> Array.iter (fun x -> (print_string ((string_of_float x)^"; "))) b;print_string "\n") a;
  print_string "]\n")

let print_floatarray a =
 ( print_string "[";
  Array.iter (fun x -> (print_float x; print_string ", ")) a;
  print_string "]\n")

let print_floatarray2 a =
 ( print_string "[";
  Array.iter print_floatarray a;
  print_string "]\n")

let print_floatarray3 a =
 ( print_string "[";
  Array.iter print_floatarray2 a;
  print_string "]\n")
  
    
let print_floatlist l =
  print_string "[ ";
  List.iter
    (fun x -> print_float x; print_string "; ") l;
  print_string "] "
let print_floatpairlist l =
  print_string "[ ";
  List.iter
    (fun (x,y) -> Printf.printf "(%f, %f); " x y) l;
  print_string "] "

let print_tensor2 x =
  let a = Tensor.to_float2_exn x in
  print_floatarray2 a
