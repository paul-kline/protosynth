

(** *this is the title

here are some comments
 *)
 
 
Tactic Notation "inv" hyp(H) := inversion H; subst.
Tactic Notation "cca" := repeat constructor; assumption.
Tactic Notation "nono" := unfold not; let nm := fresh "X" in intro nm; inversion nm.
Tactic Notation "nono" hyp(H) :=  unfold not in H; exfalso; apply H; auto.
Require Export Coq.Program.Equality.
Require Export Eqdep_dec.
Require Export Coq.Arith.EqNat.
Add LoadPath "/home/paul/Documents/coqs/protosynth".
Add LoadPath "/home/paul/Documents/coqs/protosynth/cpdt/src" as Cpdt.   
Require Export CrushEquality. 
(* Require Export Coq.Arith.Peano_dec.
 *)

 
 (*
 knowing that a lower level binds more than a higher level. Hence the level for disjunction must be higher than the level for conjunction.
 Coq < Notation "A /\ B" := (and A B) (at level 80, right associativity).
Coq < Notation "A \/ B" := (or A B)  (at level 85, right associativity).
 
 *)
 Print "=".  
Notation " x = y = z" := (x = y /\ x = z) .
Notation " x = y = z = a" := (x = y /\ x = z /\ x = a) (at level 200).
Notation " x = y = z = a = b" := (x = y /\ x = z /\ x = a /\ x = b) (at level 200).
Tactic Notation "ass" := assumption.
Tactic Notation "refl" := reflexivity. 
Tactic Notation "dest" tactic (c) := destruct c .
Tactic Notation "ind" tactic (c) := induction c. 
Tactic Notation "inv" ident(c) := inversion c; subst. 
Tactic Notation "gd" tactic (c) := generalize dependent c.
Tactic Notation "s" := simpl. 
Tactic Notation "s" ident (c) := simpl in c.
Tactic Notation "c" := constructor. 
 
Require Export String. Open Scope string_scope.
Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
Add LoadPath "/home/paul/Documents/coqs/protosynth/cpdt/src" as Cpdt.
Require Import Cpdt.CpdtTactics.

Definition xor (A : Prop) (B: Prop) := (A \/ B) /\ ~(A /\ B).



(** proof command that aids in simple proofs of equality.
 *)
Ltac equal := autounfold with unfoldEq; repeat decide equality.

(** 
Handy Ltac  for simplifying Hypothesis' since simpl doesn't do it.
Note: it will fail if the hypothesis doesn't change.
*)
Ltac simpl_H :=
 match goal with 
  [ H : ?T |- _] => progress (autounfold in H; (simpl in H))
  end.
Ltac cbn_H :=
 match goal with 
  [ H : ?T |- _] => progress (autounfold with * in H ; (cbn in H))
  end.
  
(** 
The actual command to use in proofs.
will continue to apply until it fails. 
*)
Tactic Notation "sh" := repeat simpl_H.
Tactic Notation "simplAll" := sh; autounfold; simpl.
Tactic Notation "refl" := reflexivity.


 

(*
 *)
Ltac inversion_any' := match goal with 
[H : ?x = ?y |- _] => progress ( inversion H)
end.
Ltac inversion_any := solve [(repeat inversion_any')]. 

 