From mathcomp Require Import all_ssreflect all_algebra all_field.

Import GRing.Theory Num.Theory Num.ExtraDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ab1.

Variable R : rcfType.

Open Scope ring_scope.

(*       Typical examples of elements in R        *)
Check ((-12%:~R/17%:R) : R )==  ((-12%:R/17%:R) : R).


(*                                                                           *)
(*****************************************************************************)
(* This file contains an implementation of Fortune's algorithm which follows *)
(* closely the file `python/fortun.py`.                                      *)
(* Data structures:                                                          *)
(* - Point P == (P.x , P.y)                                                  *)
(* - Arc   C == (Point, bool) | Null. `bool` is a flag to a circle event.    *)
(*               while Null is an empty arc                                  *)
(* - Beachline ==  seq Arc. The arcs in the beachline are ordered according  *)
(*                          to their occurrences according to the x-axis.    *)
(* - Edge (p_l p_r start final : Point) ( complete :bool)  ==                *)
(*   + p_l p_r are the two focal points that seperated by the edge.          *)
(*   + start & end are the end points of the edge. End may not be known,     *)
(*                                                 its default value is (0,0)*)
(*   + complete indicates that the end has been discovered.                  *)
(* - Edges == seq Edge. Not ordered                                          *)
(* - Priority Queue TODO                                                     *)
(*   + Basic idea:implement it as a Record that contains a list and an insert*)
(*     and delete functions. For insert/delete we look for max/min elemnt's  *)
(*     index then create a new list. Also, we need a check fun               *)
(* - Sweepline is defined implicitly and it moves from bottom to top.        *)
(*****************************************************************************)



Record point     : Type := Point { x :  R ;  y    : R }.
Record arc       : Type := Arc   { p : point; circle : bool}.
Record beachline : Type := Beachline { B : seq arc}.
Record edge      : Type := Edge {
  p_l   :  point ; (* Site left/*)
  p_r   :  point ; (*/Site right*)
  start :  point ;   
  final :  point ;   
  complete: bool ;   
                                }.

(* In the case of a circle event we need to know the left and the right arcs.*)
(* Else, we only need p and the fact that it's not a circle event. We assign *)
(* the default value (0, 0) to  p_l and p_r in case of a site event.         *)
(* y indicates where the event will occur, e.g. for a site event y == p.(y)  *)

Record event      : Type := Event {
  p_l :  point ; (* arc left/*)
  p   :  point ; (* Disappearing arc or a new site*)
  p_r :  point ; (*/arc right*)
   y  :    R ;   
                                   }.

(* We need to keep track of beachline, edges, and events  *)
Record track : Type := Track { ent : event; bch : beachline; edg : seq edge;
                                q  : priority_queue }.

(*---------------------------- Searching lists ------------------------------*)
(* - Check the seq.v from mathcomp *)


(*-------------------------- Geometric Functions --------------------------- *)

Definition parabolas_intersection (p1 p2 : point) : R := .
Definition vertical_intersection  := .
Definition before (p1 p2 p : point) : bool :=.
Definition search_veritcal (beachline  : seq arc) (p : point) :  := .
Definition line_intersection(l1 l2 : point ) : point :=.
Definition collinear ( p1 p2 p3 : point ):  :=.  
Definition circumcenter  ( p1 p2 p3 : point): point := .


(*------------------------- Circle event helpers ------------------------ *)

Definition check_circle_event ( ind : nat) ( y0 : real) (beachline : seq arc) 
                              ( Q : priority_queue) : seq arc :=.

Definition false_alarm (ind : nat) ( beachline : seq arc) ( Q : priority_queue) :=.

(*----------------------------   Main functions  -------------------------- *)
Definition voronoi_diagram (sites : seq point) : seq edge := .

Definition handle_site_event ( e : event)  (beachline : seq arc)(edges : seq edge) 
                             ( Q : priority_queue )   : track :=
                             .

Definition handle_site_event ( e : event)  (beachline : seq arc)(edges : seq edge) 
                             ( Q : priority_queue )   : track :=
                             .
