Require Import Coq.Classes.EquivDec.
Require Export Coq.Program.Equality.
Require Export Eqdep_dec.
 
 Create HintDb eq_dec_db. 
(**
IMPORTANT:
You MUST add each proof of equality to the eq_dec_db database
(Hint Resolve <lemma_name> : eq_dec_db.)
*)

(** 
We're going to be writing this a lot, so let's short hand it.
*)
Notation "x =<> y" := ({x = y} + {x <> y}) (at level 100).

(** 
We define a short hand for equality
*)
Definition equality (A :Type) := forall x y : A, x =<> y.  
Hint Unfold equality : unfoldEq.

Lemma eqNotation : forall A, (forall x y : A, (x =<> y)) -> (equality A).
Proof. intro. autounfold with unfoldEq. intros.  auto.
Defined.
Hint Resolve eqNotation : eq_dec_db.
   
Lemma eqNotation2 : forall A, (equality A) ->  (forall x y : A, (x =<> y)) .
Proof. intro. autounfold with unfoldEq. intros.  auto.
Defined.
Hint Resolve eqNotation2 : eq_dec_db.
(** 
The above was soooo necessary for proving x =<> y. otherwise auto can't figure out matching goal for it because it's stupid. Try 
Print HintDb eq_dec_db to see that otherwise it doesn't work properly.*)


(*  Ltac rec_eq :=
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
 *)
(**
This will eliminate an existT in a Hypothesis.
*)
Ltac kill_existT' := match goal with 
 | [ H : context[existT] |- _ ] => apply inj_pair2_eq_dec in H
end.

(** 
Why is this next bit necessary you ask? Not sure, but repeat hangs forever. Therefore we use 'do' instead and apply kill existT' at most 5 times.\
*) 
Ltac kill_existT := first [ do 5 kill_existT' 
                          | do 4 kill_existT' 
                          | do 3 kill_existT' 
                          | do 2  kill_existT' 
                          | kill_existT']. 
(**
This helps us solve the case of not equals.
*)
Ltac not_eq := let nm1 := fresh "nEq" in (let nm2 := fresh "nEq" in  ((try right); unfold not; intros nm1; inversion nm1 as [nm2];
     (try kill_existT); auto with eq_dec_db)).
     

Tactic Notation "intro_equals" := intros; autounfold with unfoldEq; intros.
 Ltac eq_dec' name x y := assert (x =<> y) as name; auto with eq_dec_db.     
Ltac dep_destruct_equality' name T := intro_equals;
 match goal with 
 | [ X : T,
     Y : T |- _] => eq_dec' name X Y end.
Ltac dep_destruct_equality name := intro_equals;
 match goal with 
 | [ x : ?X,
     y : ?X
       |- _ =<> _ ] => match goal with 
           | [ H : x =<> y |- _] => fail 1
           | _ =>  dep_destruct_equality' name X
           end 
       end.

Add LoadPath "/home/paul/Documents/coqs/protosynth/cpdt/src" as Cpdt.
Require Import Cpdt.CpdtTactics.
Tactic Notation "depEqualSolver" := (match goal with 
 | [x : ?T,
    y : ?T
          |- _ ] => (match goal with 
                   | [ |- x =<> y ] => destruct x, y
                   | _ => idtac "no need for pre-destruction"
                  end); repeat (let nm := fresh "name" in 
                     (dep_destruct_equality nm; 
                      dep_destruct nm; subst; auto with eq_dec_db) 
                   ); try not_eq
 | _ => fail "no two same types in assumptions"
 end).
 
Ltac jmeq := match goal with 
 [ H : ?T1 ~= ?T2 |- _] => apply JMeq_eq in H; auto
 end. 
Ltac jmeq_more := match goal with 
 [ jmeq : ?T1 ~= ?T2 |- {?x = ?T2} + {?x <> ?T2} ] => apply JMeq_eq in jmeq;auto
 end.

Ltac destruct_equality := intro_equals; match goal with 
 [ x : ?T,
   y : ?T |- _] => destruct (equality T)
   end.  
   
Ltac case_equals' name:= match goal with 
 [ x : ?T,
   y : ?T |- _] =>  assert ({x = y} + {x <> y}) as name; auto with *
 end. 
Tactic Notation "case_equals" := let name := fresh "equals" in case_equals' name.
Tactic Notation "no" := (unfold not; let nm := fresh "H" in intro nm; inversion nm).
 
Ltac dep_equal := intro_equals;
match goal with 
 [ x : ?T,
   y : ?T |- {?x = ?y} + {?x <> ?y} ] => dep_destruct x; dep_destruct y;
   (try (let eqName := fresh "equals" in (case_equals' eqName; destruct eqName))) ;
   (solve  [(left; subst; auto)| right; no; auto]) + jmeq + idtac "jmeq tactic failed. Destruct so that your types match!"
    
 end. 

Tactic Notation "decidable" := solve [(left; subst; auto)| right; no; auto]. 
Tactic Notation "crush_equal" := 
intro_equals; 
try decide equality;
solve [depEqualSolver; (decidable + not_eq) |  dep_equal; (decidable + not_eq)].

Theorem eq_dec_List : forall A, equality A -> equality (list A). 
Proof.  crush_equal. 
Defined. 
Hint Resolve eq_dec_List : eq_dec_db. 

Theorem eq_dec_Pair : forall A B, equality A -> equality B -> equality (A*B). 
crush_equal. 
Defined. 
Hint Resolve eq_dec_Pair : eq_dec_db. 

Theorem eq_dec_ListPair : forall A B, equality A -> equality B -> equality (list(A*B)).
crush_equal. 
Defined. 
Hint Resolve eq_dec_ListPair : eq_dec_db. 


