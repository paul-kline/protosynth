

(** *this is the title

here are some comments
 *)
 
 Require Import Coq.Classes.EquivDec.
 
Notation "x =<> y" := ({x = y} + {x <> y}) (at level 100).
 
 Ltac rec_eq :=
 match goal with
    | [ x : ?T, y : ?T |- _ ] => 
       (match T with
        | nat => generalize nat_eq_eqdec
        | bool => generalize bool_eqdec
        | unit => generalize unit_eqdec
       end) ; 
       intros X; destruct X with x y as [| paul];
       try (left; inversion e; subst; reflexivity);
       try (right; unfold complement in paul; unfold not; 
            intros Hpaul; apply paul; inversion Hpaul; reflexivity)
    end.

Ltac eqdecHelper := subst; (left; reflexivity) || (
right; unfold not; intros; inversion H; contradiction).

Tactic Notation "inv" hyp(H) := inversion H; subst.
Tactic Notation "cca" := repeat constructor; assumption.
Tactic Notation "nono" := unfold not; let nm := fresh "X" in intro nm; inversion nm.
Tactic Notation "nono" hyp(H) :=  unfold not in H; exfalso; apply H; auto.
Require Export Coq.Program.Equality.
Require Export Eqdep_dec.
Require Export Coq.Arith.EqNat.
Require Export Coq.Arith.Peano_dec.

Ltac not_eq := let x := fresh "beats" in (let y := fresh "beats" in  ((try right); unfold not; intros x; inversion x as [y];
     (try (apply inj_pair2_eq_dec in y); auto with eq_dec_db)  )). 
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
Tactic Notation "inv" tactic (c) := inversion c. 
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

(* ident string *)
 