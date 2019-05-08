(* Codes credit : Yves Bertot https://www-sop.inria.fr/members/Yves.Bertot/  *)
(* Most comments are written by me which may not be accurate nor correct!    *)
(* Mathematical components has an intuitive and consistent naming system:    *)
(* 'A' for associative, 'C' for commutative, 'D' for addition, 'r' for ring  *)
(* For more, see `ssralg.v` file in https://github.com/math-comp/math-comp   *)
(* In this file we will see how to use basic manipulations of an algebraic   *)
(* expression such as  move/collect a term, remove equal terms from the both *)
(* sides of an identity, distribute addition over multiplication, etc        *)

(* ------------------------------- setup ----------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import QArith.
From Coq Require Extraction.

Import GRing.Theory Num.Theory Num.ExtraDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section ab1.

(* The following variables are used to make the code independent of          *)
(* mathematical components.                                                  *)

Open Scope ring_scope.

Variable (R : rcfType).

Definition R' := (R : Type).

Definition mul : R' -> R' -> R' := @GRing.mul _.
Definition add : R' -> R' -> R' := @GRing.add _.
Definition sub : R' -> R' -> R' := (fun x y => x - y).
Definition opp : R' -> R' := @GRing.opp _.
Definition zero : R' := 0.
Definition one : R' := 1.

Definition R2_theory :=
  @mk_rt R' zero one add mul sub opp
   (@eq R')
   (@add0r R) (@addrC R) (@addrA R) (@mul1r R) (@mulrC R)
     (@mulrA R) (@mulrDl R) (fun x y : R => erefl (x - y)) (@addrN R).

Add Ring R2_Ring : R2_theory.

(* This tactic automates proving identities in a ring                        *)
Ltac mc_ring :=
rewrite ?mxE /= ?(expr0, exprS, mulrS, mulr0n) -?[@GRing.add _]/add -?[@GRing.mul _]/mul
   -?[@GRing.opp _]/opp -?[1]/one -?[0]/zero;
match goal with |- @eq ?X _ _ => change X with R' end; try ring.

(* ------------------------------------------------------------------------- *)
(*                                   DEMOS                                   *)

Theorem toto (x : R) :
  sqrtr ((x - 1) ^+ 3) = 
  sqrtr (x ^+ 3 - 3%:R * x ^+ 2 + x  + x + x - 1%:R).
Proof.
(* this works too :                                                          *)
(* congr (sqrtr _).
by mc_ring. *)

(* rewrite [expr](_ : _ = expr2) means replace expr with expr2, this         *)
(* replacement needs to be proved                                            *)
rewrite [(x - 1) ^+ 3](_ : _ =
              (x ^+ 3 - 3%:R * x ^+ 2 + x  + x + x - 1%:R)); last by mc_ring.
by [].
Qed.

Theorem toto2 (x : R) :
   (x - 1) ^+ 3 = x ^+ 3 - 3%:R * x ^+ 2 + x  + x + x - 1%:R.
Proof.
(* ! means do it as many as possible, (tac1, tac2, ..., tacn) means apply    *)
(* any of these tactics when it is possible                                  *)
rewrite !(exprS, expr0, mulr1, mulrBl, mulrBr, mul1r, addrA, opprB).
rewrite [1%:R](_ : _ = 1); last by []. (* 1%R and 1 live in different places *)
(* push the 1 to the right. *)
rewrite !(addrAC _ (- 1)).
(* get rid of both ones. *)
 congr (_ + _).
(* push the parentheses in additions to the right. *)
rewrite -!addrA.
(* the first and second terms, that are equal. *)
rewrite !(mulrS, addr0, mulrDl) .
rewrite mulr0n.
rewrite mul0r.
rewrite addr0.
rewrite !mul1r.
rewrite !opprD.
rewrite -!addrA.
congr (_ + (_ + _)).
rewrite (addrC x).
rewrite !addrA.
rewrite !(addrAC _ x).
by [].
Qed.

Theorem toto3 (x : R) :
   (x - 1) ^+ 3 = x ^+ 3 - 3%:R * x ^+ 2 + x  + x + x - 1%:R.
Proof.
by rewrite !(exprS, expr0, mulr1, mulrBl, mulrBr, mul1r, addrA, opprB,
    mulrS, addr0, mulrDl, opprD, mulr0n, subr0,
    (fun y => addrAC y (-1)), (fun y z => addrAC y z (- (x * x)))).
Qed.
