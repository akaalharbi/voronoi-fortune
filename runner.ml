open List
open Fortune

let rec int_to_positive n =
  if n = 1 then XH
  else 
    let half = int_to_positive (n / 2) in
    if n mod 2 = 1 then XI half else XO half;;

let int_to_z (n : int) =
  if n < 0 then Zneg (int_to_positive (-n))
  else if n = 0 then Z0
  else Zpos (int_to_positive n);;

let int_to_q (n, d) =
   {qnum = int_to_z n; qden = int_to_positive d};;

let rec from_positive = function
  | XH -> 1
  | XI p -> 2 * from_positive p + 1
  | XO p -> 2 * from_positive p;;

let from_z x =
   match x with
   | Z0 -> 0
   | Zpos x -> from_positive x
   | Zneg x -> -from_positive x;;

let from_q {qnum = n; qden = p} =
  (from_z n, from_positive p);;

let from_point (p : q point) : (int * int) * (int * int) =
  let Pair(x, y) = p in (from_q x, from_q y);;

let from_edge (x : q edge) : ((int * int) * (int * int)) *
                           ((int * int) * (int * int))  =
  match x with
  Pair(Pair(Pair(Pair(st, fn), site1), site2), b) -> 
   (from_point st, from_point fn);;
  
let print_point (x : q point) =
  match x with Pair({qnum = xn; qden = xd}, {qnum = yn; qden = yd}) ->
  print_int (from_z xn); print_string " ";
  print_int (from_positive xd); print_string " ";
  print_int (from_z yn); print_string " ";
  print_int (from_positive yd); print_string "\n";;

let print_edge (x : q edge) =
  match x with
   Pair(Pair(Pair(Pair(st, fn), s_l), s_r), complete) ->
   (if complete = True then 
      print_string "printing an edge\n"
    else print_string "printing an incomplete edge\n");
   print_point st;
   print_point fn;
   print_point s_l;
   print_point s_r;;

let print_event (x : q event) =
  match x with
  Pair(Pair(Pair(Pair(b, p_l), p_m), p_r), sweepline) ->
  (if b = Fortune.True then
    print_string "Printing circle event\n"
   else
    print_string "Printing site event\n");
  print_point p_l;
  print_point p_m;
  print_point p_r;
  print_int (from_z sweepline.qnum); print_string " ";
  print_int (from_positive sweepline.qden);
  print_string "\n";;

let int_main l =
  let qlist = List.map (fun (x, y) -> Pair(int_to_q x, int_to_q y)) l in
  let Pair(Pair(_, x), _) = main' qlist in 
    x;;

(* let sample_data =
[((-23, 1), (-15, 1)); ((-10, 1), (-12, 1)); ((-27, 1), (-69, 1));
 ((-69, 1), (-96, 1)); ((74, 1), (44, 1)); ((84, 1), (-88, 1));
 ((95, 1), (85, 1)); ((-77, 1), (-42, 1)); ((17, 1), (-65, 1)); 
 ((35, 1), (12, 1)); ((62, 1), (-8, 1)); ((59, 1), (-85, 1));
 ((-17, 1), (76, 1)); ((-78, 1), (-55, 1)); ((34, 1), (-68, 1));
 ((97, 1), (55, 1)); ((34, 1), (95, 1)); ((-98, 1), (-51, 1));
 ((-5, 1), (57, 1)); ((62, 1), (-50, 1)); ((-77, 1), (-99, 1));
 ((3, 1), (-2, 1)); ((-81, 1), (-18, 1)); ((-49, 1), (77, 1));
 ((56, 1), (26, 1)); ((61, 1), (-42, 1)); ((-56, 1), (35, 1));
 ((19, 1), (57, 1)); ((18, 1), (4, 1)); ((-81, 1), (83, 1))];; *)

let sample_data = [((-23, 1), (-15, 1)); ((-10, 1), (-12, 1))];;

let result = int_main sample_data;;

List.iter print_edge result;;

