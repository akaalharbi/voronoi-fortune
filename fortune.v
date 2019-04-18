From mathcomp Require Import all_ssreflect all_algebra all_field.
Require Import QArith.
From Coq Require Extraction.

Import GRing.Theory Num.Theory Num.ExtraDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section ab1.

(* The following variables are used to make the code independent of
  mathematical components. *)
Variables (R : Type) (one zero : R)
  (add mul : R -> R -> R) (opp inv sqrtr : R -> R).
Variables (eq ler ltr : R -> R -> bool) (natr_mul exp : R -> nat -> R).


Notation "x + y" := (add x y) : a_scope.
Notation "x * y" := (mul x y) : a_scope.
Notation "x - y" := (add x (opp y)) : a_scope.
Notation "x / y" := (mul x (inv y)) : a_scope.
Notation "x >= y" := (ler y x) : bool_scope.
Notation "x <= y" := (ler x y) : bool_scope.
Notation "x < y" := (ltr x y) : bool_scope.
Notation "x > y" := (ltr y x) : bool_scope.
Notation "x == y" := (eq x y) : bool_scope.
Notation "x *+ n" := (natr_mul x n) : a_scope.
Notation "x ^ n" := (exp x n) : a_scope.
Notation "- x" := (opp x) : a_scope.
Notation "n %:R" := (natr_mul one n) : a_scope.

Open Scope a_scope.

(*****************************************************************************)
(* This file contains an implementation of Fortune's algorithm which follows *)
(* closely the file `python/fortun.py`.                                      *)
(* Convention: m l r stands for middle, left, and right.                     *)
(* Data structures :                                                         *)
(* - Point P == (P.x , P.y)                                                  *)
(* - Arc   C == (Point, bool) | Null. `bool` is a flag to a circle event.    *)
(*               while Null is an empty arc                                  *)
(* - Beachline ==  seq Arc. The arcs in the beachline are ordered according  *)
(*                          to their occurrences according to the x-axis.    *)
(* - Edge (start final p_l p_r : Point) ( complete :bool)  ==                *)
(*   + p_l p_r are the two focal points that seperated by the edge.          *)
(*   + start & end are the end points of the edge. End may not be known,     *)
(*                                                 its default value is (0,0)*)
(*   + complete indicates that the end has been discovered.                  *)
(* - Edges == seq Edge. Not ordered                                          *)
(* - Event (cir : bool) (p_m p_l p_r : point) (sweepline : R)                *)
(*   + cir is true when it's a circle event                                  *)
(*   + When cir: then p_m will disappear while p_l and will intersect        *)
(*   + Otherwise, p_l and p_r are dummy variables to preserve the type       *)
(* - Priority Queues  == seq event.                                          *)
(*   + push (e : event) (Q : seq event) == adds according to its priority    *)
(*   + pop removes the head of Q and return (h, Q-h)                         *)
(* - Dummy instances were defined to deal with the base cases                *)
(* - Sweepline is defined implicitly and it moves from bottom to top.        *)
(* - Arc_ind (i1, i2, both ) tells whether a site lies above two arcs or     *)
(*   an arc. Also, i1 and i2 are the arc indices in the beachline.           *)
(*****************************************************************************)

(*======================== Data Structures : =============================== *)

(* Point *)
Definition point          : Type := (R * R)%type.
Definition Point(x y : R) : point := (x, y).
Notation "p .x" := (fst p) ( at level 60).
Notation "p .y" := (snd p) ( at level 60).

Definition point_eq (p1 p2 : point) : bool :=
  (p1.x == p2.x) && (p1.y == p2.y).

Notation "p1 === p2" := (point_eq p1 p2)
  (at level 70, no associativity) : a_scope.

Definition geq (p1 p2 : point ) : bool :=
  if (p1.y) >= (p2.y) then true 
  else if ( (p1.y) == (p2.y) ) &&  ( (p1.x) >= (p2.x) ) then true 
  else false.
Definition less (p1 p2 : point) : bool :=
  if geq p1 p2 then false else true.

(* Arc *)
Definition arc   : Type := (point * bool)%type.
Definition Arc (p: point) ( c : bool) : arc := (p, c).
Definition focal (p : arc) := fst p.

Notation "p .focal"  := (focal p) ( at level 81).  (* same as p.x *)
Notation "p .circle" := (snd p) ( at level 81). (* Do I need to define another *)
                                            (* fst, so focal & x are disjoint?*) 

(* Edge *)
Definition edge  : Type := (point * point * point * point * bool)%type.
Definition Edge  (st  fn  s_l  s_r  : point ) ( c : bool) : edge :=
                 (st, fn, s_l, s_r, c).
Notation "p .complete" := (snd p) ( at level 82).
Notation "p .r"  := (snd (fst p)) ( at level 82). (* p/Right site *)
Notation "p .l"  := (snd (fst (fst p))) ( at level 82). (* Left site/p  *)
Notation "p .fn" := (snd (fst (fst (fst p)))) ( at level 82). (* Final point *)
Notation "p .st" := (fst (fst (fst (fst p)))) ( at level 82). (* Start point *)


(* Event *)
Definition event  : Type := ( bool * point * point * point * R )%type.
Definition Event  (b : bool) ( p_m  p_l  p_r : point) ( sweepline : R) : event :=
                  (b, p_l, p_m, p_r, sweepline).
Definition nulEv := Event false (Point 0%:R 1%:R) (Point 2%:R 3%:R) 
                                (Point 4%:R 5%:R)  6%:R.
Notation "p .swp" := (snd p) ( at level 82).             (* Sweepline   *)
Notation "p .r"   := (snd (fst p)) ( at level 82).       (* m{Right arc *)
Notation "p .m"   := (snd (fst (fst p))) ( at level 82). (* Left arc}m  *)
Notation "p .l"   := (snd (fst (fst (fst p)))) ( at level 82). (* Final point *)
Notation "p .cir" := (fst (fst (fst (fst p)))) ( at level 82). (* Start point *)
(* cir  is an unfortunate notation *)

(* Priority Queue *)
Fixpoint push (e : event) ( s : seq event) : seq event   := 
  match s with 
  | [::] => [:: e]
  | h::t =>  if  ( geq (h.m)  (e.m) ) then (* The y-coordinate of the site *)
              e :: h :: t
             else h :: push e t
  end.
Definition pop   ( s : seq event) := ( head nulEv s, drop 1 s).
Definition empty ( s : seq event) := if size s is 0%nat then true else false.


(* Arc_ind  *)
Definition arc_ind : Type    := (nat * nat * bool ).
Definition Arc_ind (ind1 ind2: nat) ( both : bool) : arc_ind := 
                   (ind1, ind2, both ).
Notation "p .both" := (snd p) (at level 84).
Notation "p .ind2" := (snd ( fst p)) (at level 84).
Notation "p .ind1" := (fst ( fst p)) (at level 84).
(* Eval compute in Arc_ind 1 2 true .*)
Definition add_ind ( i1 i2 : arc_ind) := 
  Arc_ind ((i1.ind1) + (i2.ind1)) ( (i1.ind2) + (i2.ind2)) 
          ( orb (i1.both)  (i2.both)).
Definition is_empty T ( s : seq T) : bool := 
  match s with [::] => true | h::t => false end.

(* ------------------------------ Nulls ------------------------------------ *) 
Definition nulArc := Arc (Point 1%:R 2%:R) false.
(* nulEv is defined above *)
(* Definition nulEv := Event false (Point 0%:R 1%:R) (Point 2%:R 3%:R)
                                (Point 4%:R 5%:R)  6%:R.*)
                                
Definition nulEd : edge := Edge (Point 1%:R 2%:R) (Point 1%:R 2%:R)
                                (Point 1%:R 2%:R) (Point 1%:R 2%:R) true.
                                
Definition emEd : seq edge  := [::]. (* Empty list of edges *)

Definition emQ  : seq event := [::]. (* Empty Queue of event *)

Definition emB  : seq arc   := [::]. (* Empty beachline      *)





(* -------------------------- seq functions -------------------------------- *)
(* They always return an index or a seq of the same type                     *)

Fixpoint insert T (a : T) (s : seq T) (i : nat)  : seq T :=
  (* insert a into T at ith position *)
  match i with
  | 0%nat   => a  ::  s
  | S n => match  s with 
           | h :: t => h :: (insert  a t n)
           | _      =>  [:: a]
           end
  end.

Fixpoint remove T (i : nat) (s : seq T) : seq T :=
  match i, s with
  | 0%nat , h::t  => t
  | 0%nat , _     => [::]
  |S n, h::t => remove n t
  | _ , _    => [::]
  end.  


Fixpoint search_3  (p1 p2 p3 : point) (s : seq point) {struct s}: nat :=
 (* TODO make it polymorphic.                                                *)
 (* Given a sequence s, returns the index of p2 in s where p1 is perceded by *)
 (* p1 and followed by p3.                                                   *)
 (* Notice it returns a correct result if p1 p2 p3 are in s                  *)
  match s with 
  | h1 :: t => match t with 
              | h2 :: t2  => match t2 with  (* The main case *)
                             | h3 :: t3 => 
                                          if (p1 === h1) && (h2 === p2)
                                             && (h3 === p3)         then 1%nat
                                          else 
                                                (1+ (search_3  p1 p2 p3 t))%nat
                             |  _ => 0 (* p1 p2 p3 are not in s *)
                             end       (* thus probably a wrong result *)
              | _ => 0
              end
  | _ => 0
  end. 


Definition search_beach (p1 p2 p3 : point) ( beachline : seq arc): nat :=
   let beachFocals := map (fun  x => x.focal) beachline in
   search_3 p1 p2 p3 beachFocals.

Definition search_edges (edges : seq edge) (p1 p2: point) : nat :=
(* Given a list of edges, a left site p1, right site p2 then it returns the *) 
(* the index where p1 p2 are the sites seperated by the edge                *)
  find (fun x => (x.l === p1) && (x.r === p2)) edges.


(* ========================== Geometric Functions ========================== *)

Definition midpoint  ( p1 p2 : point) : point := 
  Point  ( ((p1.x)+(p2.x))/2%:R )   ( ((p1.y)+(p2.y))/(2%:R) )  .


Definition direction ( p1 p2 : point) : point := 
  (* The directed vectro that originates from p1 and ends at p2 *) 
  Point ((p1.x)-(p2.x))   ((p1.y)-(p2.y)).

Definition dot_prod ( p1 p2 : point) : R :=  (p1.x)*(p2.x) + (p1.y)*(p2.y).

Definition line (n p : point ) : R*point := 
  (* l : n . (x - x0) = 0 => n.x = n.x0, we keep n.x0 and n *) 
  ( dot_prod n p, n).

Definition bisector ( p1 p2 : point) : R*point :=
  (* The line that passes through (midpoint p1 p2), *) 
  (*  and normal to (direction p1 p2)               *)
  line (direction p1 p2) (midpoint p1 p2).


Definition line_intersection  ( l1 l2 : R*point) : point :=
  (* l1 : a1*x + b1*x = c1 *)
  (* l2 : a2*x + b2*x = c2 *)
  let a1 := ( fst ( snd l1 )) in
  let b1 := ( snd ( snd l1 )) in
  let a2 := ( fst ( snd l2 )) in
  let b2 := ( snd ( snd l2 )) in
  let c1 := -(fst l1)       in
  let c2 := -(fst l2)       in
  let x  := ( (c1*b2 - b1*c2) / (a1*b2 - b1*a2) ) in
  let y  := ( (a1*c2 - c1*a2) / (a1*b2 - b1*a2) ) in
  Point x y.

Definition collinear ( p1 p2 p3 : point ): bool :=   
  if       (p1 === p2) || (p2 === p3) || (p3 === p1)       then true
  else if  ( (p1.y)  ==  (p2.y) ) && ( (p2.y) ==  (p3.y) ) &&
           ( (p3.y)  ==   0%:R  )                       then true
  else if  ( ((p1.x) / (p1.y))  ==  ((p2.x) / (p2.y)) )    &&
           ( ((p2.x) / (p2.y))  ==  ((p3.x) / (p3.y)) ) then true
  else false.


Definition circumcenter ( p1 p2 p3 : point ) : point :=
  let    midp1p2 := midpoint p1 p2 in
  let    midp2p3 := midpoint p2 p3 in
  let bisectp1p2 := bisector p1 p2 in
  let bisectp2p3 := bisector p2 p3 in
  line_intersection bisectp1p2 bisectp2p3 .


 
(*-------------------------- Parabolas Functions --------------------------- *)
(* (a+sqrt(disc))/b is a solution to the quadratic equation of equating two  *)
(* parabolas                                                                 *)

Definition a (p1 p2 : point) ( y0 : R) : R :=
   (p2.x) * (p1.y)  -  (p1.x) * (p2.y)  + ( (p1.x)  -  (p2.x) )*y0.

Definition b ( p1 p2 : point) ( y0 : R) : R := ( (p1.y)  -  (p2.y) ).

Definition disc ( p1 p2 : point) ( y0 : R) : R :=
  sqrtr ( (2%:R) * (p1.y) ^2* (p2.y) ^2 +  (p1.y) * (p2.y) ^3 +
  ( (p1.x) ^2 - (2%:R)* (p1.x) * (p2.x)  +  (p2.x) ^2 +
  (p1.y) ^2 - (2%:R)* (p1.y) * (p2.y)  +  (p2.y) ^2)*y0^2 +
  ( (p1.y) ^3 + ( (p1.x) ^2 - (2%:R)* (p1.x) * (p2.x)  +
  (p2.x) ^2)* (p1.y) )* (p2.y)  - ( (p1.y) ^3 -  (p1.y) * (p2.y) ^2 +
  (p2.y) ^3 + ( (p1.x) ^2 - (2%:R)* (p1.x) * (p2.x)  +  (p2.x) ^2)* (p1.y)
  + ( (p1.x) ^2 - (2%:R)* (p1.x) * (p2.x)  +  (p2.x) ^2 -
  (p1.y) ^2)* (p2.y) )*y0).

 
Definition par_inter_p (p1 p2 : point) (y0 : R) : R := 
  (* Returns the largest solution of two parabolas intersection *)
  if  (p1.y)  ==  (p1.y)  then  (( (p1.x) + (p2.x) )/(2%:R)) 
  else ((a p1 p2 y0) + (disc p1 p2 y0))/(b p1 p2 y0) .
(* minus *)
Definition par_inter_m (p1 p2 : point) (y0 : R) : R := 
    (* Returns the smallest solution of two parabolas intersection *)
  if  (p1.y)  ==  (p1.y)  then  (( (p1.x) + (p2.x) )/(2%:R)) 
  else ((a p1 p2 y0) - (disc p1 p2 y0))/(b p1 p2 y0) .


Definition vertical_intersection (par site : point) : point := 
  (* Given a point p1 and a parabola P above/below it.   *)
  (* Return the intersection point between y = p.y and P *)
  let y := ( ((par.x)- (site.x))^2+ (par.y)^2   -
             (site.y)^2)/( (2%:R)*( (par.y) - (site.y))) in
  (Point (site.x) y).

Definition maxR (a1 a2 : R) : R := 
if a1 >= a2 then a1 else a2.
Definition minR (a1 a2 : R) : R := 
if a1 < a2 then a1 else a2.


Definition pick_sol (p1 p2 : point) (y0:R) : R :=
  (* This function picks the right or left intersection according to *)
  (* whether p1 discovered before p2 or not.                         *)
  if geq p1 p2 then minR (par_inter_p p1 p2 y0) ( par_inter_m p1 p2 y0)
  else  maxR (par_inter_p p1 p2 y0) ( par_inter_m p1 p2 y0).


Definition before (p1 p2 p : point) : bool*bool :=
  (* Pick the suitable intersection point *) 
  let sol  := pick_sol p1 p2 (p.y)  in
  if      sol  > (p.x) then (true, false)
  else if sol == (p.x) then (true, true)
  else (false, false).


Fixpoint search_veritcal (beachline  : seq arc) (q : point) {struct  beachline}
                         :  arc_ind  :=

  let one  := Arc_ind 1 1 false in
  let zero := Arc_ind 0 0 false in

  match beachline with
  | [::] => zero 
  |  h1 :: t => match t with (* two matches was the trick to avoid the error *)
              | [::] => zero
              | h2 :: t2 =>
                            let b := before (h1.focal) (h2.focal) q in
                            if (b.1) && (b.2) then Arc_ind 1 2 true
                            else if (b.1)     then Arc_ind 1 1 false
                            else add_ind one  (search_veritcal   t  q )
               end
   end.






(* ----------------------------  event helpers ----------------------------- *)


Definition check_circle_event ( ind : nat) ( y0 : R) (beachline : seq arc) 
                              (Q : seq event) : ( (seq arc) * (seq event) ) :=
  let l := (nth nulArc beachline (ind -1)).focal in
  let m := (nth nulArc beachline (ind)).focal    in
  let r := (nth nulArc beachline (ind +1)).focal in
  if  (eqn ind 0)%N || ( is_empty beachline )  then (beachline, Q)
  
  else if (collinear l m r) || 
      ((( (m.y) - (l.y))*( (r.x) - (l.x)) - ( (r.y) - (l.y))*( (m.x) - (l.x)))
       > 0%:R )
     then (beachline, Q)

  else 
       let c := circumcenter l m r                                   in
       let rad := sqrtr ( ((c.x) - (m.x))^2   + ((c.y) - (m.y))^2 )  in
       let upper := rad + (c.y)                                      in
       if  upper < y0 then (beachline, Q)
       else 
            let update   := Arc m true                            in
            let newBeach := set_nth nulArc beachline ind update   in
            let newEvent := Event true l m r (m.y)                in
            let newQ     :=  (push newEvent Q)           in
            (newBeach, newQ).

Check (fun x : event =>  fst (fst (fst (fst x)))).

Definition event_eq (e1 e2 : event) :=
  (snd e1 == snd e2) &&
  (snd (fst e1) === snd (fst e2)) &&
  (snd (fst (fst e1)) === snd (fst (fst e2))) &&
  ((snd (fst (fst (fst e1)))) === (snd (fst (fst (fst e2))))) &&
  (eqb (fst (fst (fst (fst e1))))   (fst (fst (fst (fst e2))))).

Definition false_alarm (ind : nat) ( beachline : seq arc) ( Q : seq event) :
                       (seq arc)* (seq event) := 
  let current := nth nulArc beachline ind in
  let cond    := (current.circle)         in
  if (~~ cond) then
       (beachline, Q)
  else
      let update   := Arc (current.focal) false                    in
      let newBeach := set_nth nulArc beachline ind update          in
      let left     := (nth nulArc beachline (ind -1)%nat ).focal   in
      let right    := (nth nulArc beachline (ind +1)%nat ).focal   in
      let mid      := (nth nulArc beachline ind ).focal            in
      let l_m_r    := Event true mid left right (mid.y)            in
      let newQ     := filter (fun x =>  ~~ event_eq x l_m_r) Q     in
     (newBeach, newQ).



(*-----------------------------  Main functions  -------------------------- *)


Definition special_case (ind       :     nat)   (p3    : point   )
                        (beachline : seq arc)   (edges : seq edge)   :
                        (      seq arc      ) * (    seq edge    )   :=
  let p1       := (nth nulArc beachline ind).focal           in
  let p2       := (nth nulArc beachline (ind + 1)%nat).focal in
  let pos      := vertical_intersection p1 p3                in
  let edg_ind  := search_edges edges p1 p2                   in
  let e1       := nth nulEd edges edg_ind                    in
  let e1Upd    := Edge (e1.st) pos (e1.l) (e1.r) true        in
  let updEdges := set_nth nulEd edges edg_ind e1Upd          in
  let e2       := Edge (pos) (pos) (p3) (p2) false           in
  let e3       := Edge (pos) (pos) (p1) (p3) false           in
  let newArc   := Arc (p3) false                             in
  let newBeach := insert  newArc beachline (ind + 1)%nat     in
  let newEdges := updEdges ++ [:: e2; e3]                    in
  (newBeach, newEdges).


Definition handle_site_event ( p1   : point   ) ( beachline : seq arc )
                             (edges : seq edge) ( Q         : seq event) :
                             ((seq arc) * ( seq edge) * ( seq event))    :=
                               (*  beach       edges          Q *)

  let indices := search_veritcal beachline p1 in
  let i       := indices.ind1                 in
  if ( indices.both )  then
      (* The special case doesn't affect the events queue *)
      (( special_case i p1 beachline edges ),  Q)
  else
      let arc_above := (nth nulArc beachline i).focal            in
      let check     := (false_alarm i beachline Q)               in
      let chBeach   := (check.1)                                 in
      let chQ       := (check.2)                                 in
      let pos       := vertical_intersection arc_above p1        in
      let e1        := Edge (pos) (pos) (p1) (arc_above) false   in
      let e2        := Edge (pos) (pos) (arc_above) (p1) false   in
      let newEdges  := edges ++ [:: e1; e2]                      in
      let newArc    := Arc p1 false                              in
      let up1B      := insert newArc beachline (i + 1)%nat       in
      let up2B      := insert (Arc p1 false) up1B (i + 1)%nat    in
      let y0        := p1.y                                      in
      let BeaQ_l    := check_circle_event i y0 up2B chQ          in
      let B_l       := (BeaQ_l.1)   in  let Q_l := (BeaQ_l.2)    in
      let BeaQ_r    := check_circle_event (i + 2)%nat y0 B_l Q_l in
      let newBeach  := BeaQ_r.1                                  in
      let newQ      := BeaQ_r.2                                  in
      (newBeach, newEdges, newQ) .

Definition handle_circle_event (ev    : event   ) (beachline : seq arc  )
                               (edges : seq edge) (Q         : seq event) :
                               ( (seq arc) * ( seq edge) * ( seq event) ) :=
  let y0        := ev.swp                                        in
  let l         := ev.l                                          in
  let m         := ev.m                                          in
  let r         :=  ev.r                                         in
  let c         := circumcenter l m r                            in 
  let e1        := Edge (c) (c) (l) (r) false                    in 
  let e_ind_l_m := search_edges edges l m                        in
  let e_ind_m_r := search_edges edges m r                        in
  let e_l_m     := (nth nulEd edges e_ind_l_m)                   in
  let e_m_r     := (nth nulEd edges e_ind_m_r)                   in
  let e_l_m'    := Edge (e_l_m.st) (c) (e_l_m.l) (e_l_m.r)  true in
  let e_m_r'    := Edge (e_m_r.st) (c) (e_m_r.l) (e_m_r.r)  true in
  let newEdges  := set_nth nulEd edges e_ind_l_m e_l_m'          in
  let newEdges' := set_nth nulEd newEdges e_ind_m_r e_m_r'       in
  let i         := search_beach l m r beachline                  in
  let beach'    := remove i beachline                            in
  let i_left    := (i - 1)%nat                                   in
  let i_right   := i%N                                           in
  let BeaQ_l    := check_circle_event i_left y0 beach' Q         in
  let B_l       := (BeaQ_l.1)   in  let Q_l := (BeaQ_l.2)        in
  let BeaQ_r    := check_circle_event i_right y0 B_l Q_l         in
  let newBeach  := BeaQ_r.1                                      in
  let newQ      := BeaQ_r.2                                      in
  (newBeach, newEdges', newQ) .




Fixpoint fortune  (n     :  nat    ) (beachline : seq arc  )
                  (edges : seq edge) (Q         : seq event) 
                  {struct n        }                             :
                  (nat * (seq arc) * ( seq edge) * ( seq event)) :=

  match n, Q with
  | _    , [::] => (n, beachline, edges, Q)
  | S n' , h::t => if (h.cir) then
                       let res := handle_circle_event h beachline edges Q in
                       let edges' := snd (fst res)  in
                       let beach' := fst (fst res)  in
                       let Q'     := snd res        in
                       fortune n' beach' edges' Q'
                   else
                       let res := handle_site_event (h.m) beachline edges Q in
                       let edges' := snd (fst res)  in
                       let beach' := fst (fst res)  in
                       let Q'     := snd res        in
                       fortune n' beach' edges' Q'

  | 0%nat , _    => (n, beachline, edges, Q)
  end.

Lemma fortune_step n beachline edges Q : fortune n beachline edges Q =
    match n, Q with
  | _    , [::] => (n, beachline, edges, Q)
  | S n' , h::t => if (h.cir) then
                       let res := handle_circle_event h beachline edges Q in
                       let edges' := snd (fst res)  in
                       let beach' := fst (fst res)  in
                       let Q'     := snd res        in
                       fortune n' beach' edges' Q'
                   else
                       let res := handle_site_event (h.m) beachline edges Q in
                       let edges' := snd (fst res)  in
                       let beach' := fst (fst res)  in
                       let Q'     := snd res        in
                       fortune n' beach' edges' Q'

  | 0%nat , _    => (n, beachline, edges, Q)
  end.
Proof. by case: n. Qed.

Fixpoint init (s : seq point) (Q : seq event): seq event := 
  match s with 
  | h::t => let h_ev := Event false h h h (h.y) in
            init t (push h_ev Q)
  | _    => Q
  end.

Definition main (s : seq point)  :=
  let Q := init s emQ              in
  let n := ((size Q)*5)%nat        in (* TODO Find an accurate upper bound *)
  let res := fortune n emB emEd Q  in (* To add an extra box *)
  res.
  
End ab1.

(* Now we shall make the code rely on rational computations. *)

(* This is a square root function that should give 32 bits of precision. *)
Definition Qsqrt (a : Q) : Q:=
  let n := Qnum a in let d := Zpos (Qden a) in
  let d' := Z.sqrt (d * 2 ^ 64) in
  let n' := Z.sqrt (n * 2 ^ 64) in
  let g := Z.gcd n' d' in
  let d'' := match (d' / g)%Z with Zpos d'' => d'' | _ => xH end in
    ((n' / g) # d'').

Definition Qexp (a : Q) (n : nat) :=
  Qpower a (Z.of_nat n).

Definition Qnatmul (a : Q) (n : nat) :=
  inject_Z (Z.of_nat n) * a.

Definition Qlt_bool (a b : Q) := Qle_bool a b && ~~ Qeq_bool a b.

Definition main' := main (1 : Q)
  Qplus Qmult Qopp Qinv Qsqrt Qeq_bool Qle_bool Qlt_bool Qnatmul Qexp.

Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "fortune.ml" main'.

(* This produces files fortune.ml and fortune.mli 
   These can be used with a stub file that is also provided in
   the sources: file runner.ml.
   To execute this code outside Coq you can:
     ocamlc fortune.mli
     ocamlc fortune.ml
     ocamlc -o runner fortune.cmo runner.ml
   this produces a file runner that you can execute
   Alternatively, you can also load the functions in an ocaml interpreter:
     ocamlc fortune.mli
     ocamlc fortune.ml
     ocaml fortune.cmo
        #use "runner.ml";;

   You are then in an interpreter, where you can call the functions one by
   one for tests.  Beware they they may have changed names, because Coq names
   are not always acceptable for ocaml functions and constructors.  *)

(* Alternatively, you can run the functions directly inside Coq, as follows. *)

Definition small_data := [:: ((-23)#1, (-15)#1)].

Definition result :=  main' [:: ((-23)#1, (-15)#1)].

Check snd (fst result) : seq (edge Q).
Compute length result.1.2.
(* In the current version, for a single site, the program produces 14 edges.
   This is obviously wrong. *)

Compute emEd.

Definition handle_site_event' :=
  handle_site_event (1 : Q) Qplus Qmult Qopp Qinv Qsqrt
   Qeq_bool Qle_bool Qlt_bool Qnatmul Qexp.

Definition init' := init Qeq_bool Qle_bool.

Compute init' small_data nil.

Definition q1 := Eval compute in init' small_data nil.

(* Here is an example of how one can scrutinize the execution step by step. *)

Lemma test : main' small_data = (0%nat, nil, nil, nil) (* this a dummy value. *).
(* Unfold the main functions. *)
rewrite /main' /main.
(* Notice that I added the fortune_step lemma exactly for this purpose. *)
(* Note that the last argument of fortune is q1. *)
rewrite -[(init _ _ _ _)]/q1.
rewrite fortune_step.

set aa := (muln _ 5).
have -> : aa = 5%nat by [].
(* expand the value of one variable. *)
rewrite /small_data.
(* re-collapse the value of a variable. *)
rewrite -/small_data.
(* To find the value that ab should have, I perform the following mock proof.
   have : ab = [::].
     compute.
   This gives me an unprovable goal, where the left-hand side is the exact value
   of ab.  I copy this left hand side in the next tactic. *)
rewrite /q1.
set ac := (false, _, _, _, _).1.1.1.1.
(* here guessing the value of ac is easy, I still record it in the script. *)
have -> : ac = false by [].
(* I use the definition handle_site_event' to make the goal slightly easier
  to read. *)
rewrite -/handle_site_event'.
(* To make goals easier to read, I decide to abbreviate the point that appears
  many times as just p. *)
set p := ((_ # _), _).
rewrite -/handle_site_event'.
(* I will also do the same for the event that appears several times. *)
set e := (false, p, p, p, -15 # 1).
set ad := _.1.1.2.
have -> : ad = (-23 # 1, -15 # 1) by [].
rewrite -/p.
set ae := handle_site_event' _ _ _ _.
set px := -23#1.
set y1 := 355 # 34.
set e1 := (px, y1, (px, y1), p, (1, 2 # 1), false).
set e2 := (px, y1, (px, y1), (1, 2 # 1), p, false).
have  -> : ae = ([::(p,false);(p,false)], [:: e1; e2], q1) by [].
rewrite {2}/snd.
(* Here not that again, the last element of fortune is q1: this is a bug. *)
rewrite fortune_step.
