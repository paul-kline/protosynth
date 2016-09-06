

Fixpoint p1 (n : nat) : nat :=
match n with
 | O => O
 | S x => p1 x
end.

(*
Fixpoint p2 (n: nat) : nat :=
match n with
 | O => 0
 | S x => p2 (p1 n)
end. 
*)
Theorem one : forall x : nat, p1 x = O .
intros; induction x; try reflexivity; simpl; auto. Qed.

(* Don't worry! We can fix this problem on our own. Let's look at the
actual Definition of Fix so we can make one ourselves. *)
Check Fix.
(*
Fix
     : forall (A : Type) (R : A -> A -> Prop),
       well_founded R ->
       forall P : A -> Type,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, P x

What is this well_founded thing? What is this 'R'? WELL, well_founded-ness is how Coq 
proves to itself that this function will eventually end. Thereby, making it legal
in it's calculus of constructive logic (no infinite regression!).  
Here's what we're going to do:
In order to define this recurisive function, we need to prove that each recursive call
to this function is given a 'smaller' argument. So the relation 'R' is going to be a
relation that is essentially an "is less than" relation. Of course, any old relation
could have the type 'A -> A -> Prop', but only one that defines this 
monotonic decreasing behavior I speak of will be able to satisfy the 
'well_founded R' construction as required by Fix.  
Let's now look at the definition
of well_founded. 

*) 
Print Fix. 
Print well_founded.
Print Acc.
(*
well_founded = 
fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
     : forall A : Type, (A -> A -> Prop) -> Prop

Argument A is implicit

Remember 'Argument A is implicit' means we don't actually have to provide that argument. 
Coq is smart enough to figure it out in this case from the types provided in the R
relation. 

Perhaps the type is better written with parens like this:
well_founded = 
fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
     : (forall A : Type, (A -> A -> Prop) ) -> Prop

You'll see why this is helpful in a minute. 

Let's say what well_founded says in people-speak.
 'well_founded' is a function that takes a relation 'R' and gives you back a proof
(  forall a : A, Acc R a
     : forall A : Type, (A -> A -> Prop) -> Prop). 

We know this is a proof since it gives us back a Prop. So 'well_founded' is a 
function that takes a relation 'R' and gives us back a proof that states that for
every single constructable thing of type A there is an accessibility thing (Acc R a). This 
accessibility thing has type (forall A : Type, (A -> A -> Prop). We are finally getting to
the bottom of this! Let's look at the INDUCTIVE type Acc. 

Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x

Finally, we are looking at something that in its definition doesn't introduce something else we haven't
seen before! What does Acc say in English? Acc is an inductive type of type Prop ( Acc .... : Prop).
It is 'indexed' over an 'A' which has type 'Type', a relation 'R' (which we've talked about), and a
particular thing of type A. To make an Acc there is only one consstructor, 'Acc_intro' which must be 
provided with a proof that for all (any) element of type A, if y is "less than" x, y is 
accessible (Acc R y).
And that's it! Now that we've explored all the way to the bottom of the chain, we can start building our
way all the way back up to Fix.
So, let's start with 'R'. the 'A' type in R is the type of the argument that we must prove decreases.
In this example, we are trying to prove this for a function over nats.*)


Definition myR (n1 : nat) (n2 : nat) : Prop := n1 < n2. 
(*Let's make sure we got that type right. Remeber 'A' is nat in our case. *)
Check myR.
(* Looks good! Now we need to create the accessibility inductive type for our relation.
*)

Theorem zeroAccssible : Acc myR 0.
constructor. intros. constructor. intros. inversion H. Qed.

Theorem oneAcc : Acc myR 1. constructor.  intros. constructor. inversion H.
subst. intros. inversion H0. subst. intros. inversion H1.
Qed.
Theorem dosAcc : Acc myR 2.
constructor. intros. inversion H. subst. apply oneAcc. subst. inversion H1. apply zeroAccssible.
subst. inversion H2. Defined.

Theorem PrevIs : forall x : nat, Acc myR (S x) -> Acc myR (x).
intros. inversion H. apply H0. unfold myR. auto. Qed.

Theorem PrevIs2 : forall x y : nat, Acc myR x -> myR y x -> Acc myR y.
Proof. intro. intros. induction H. apply H. assumption.
Qed.


Add LoadPath "C:\Users\Paul\Documents\coqs\protosynth\cpdt\src". 
Require Import CpdtTactics. (* 
Theorem SuccIs : forall x : nat, Acc myR x -> Acc myR (S x). Proof.  intros. apply H.  constructor. intros.

 destruct H0. destruct H0 eqn:hfeihf.     crush. 
induction H.   apply Acc_intro. intros. apply H.    
induction (S x). constructor. intros. inversion H0. constructor. intros.    subst.    inversion H. constructor. intros. apply H0.    apply H0.   
eapply PrevIs2 in H . constructor. apply H. unfold myR. eauto.   inversion H.    .  constructor. intros.   induction x. constructor. intros. inversion H0. subst.
constructor. intros. inversion H1. subst. inversion H2. constructor. intros.            eauto.   induction H.
apply H0.  
constructor. intros. apply prevIs2.     *)

Require Import EqNat. 

Print "<".

Theorem allAcc : forall x : nat, Acc lt x.
Proof. intros.  induction x. apply zeroAccssible. constructor.
intros. destruct y. apply zeroAccssible. inversion H. subst. assumption. subst.
destruct IHx. constructor. apply H0. auto.
Qed.
Print well_founded.

Definition mywfr : well_founded lt. constructor. apply allAcc. Qed.
Print Fix.

Definition myf : nat -> nat.
 refine 
   (Fix mywfr (fun _ => nat)
      (fun (x : nat)
        (subcall : forall x' : nat, lt x' x -> nat) =>
          _)
            ). destruct x eqn:xval. exact x. apply subcall with n.
            auto. Qed.

Check myf. 

(* I need well_founded myRelation. *)
Fixpoint p2 (n : nat) : nat :=
match n with
 | O => O
 | S x => p2 (p1 x)
end.