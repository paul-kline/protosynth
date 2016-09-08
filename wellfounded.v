(** * Intro
  So you've run into despare.. You want to define a fixpoint (recursive) function in Coq, but instead of the beautiful green line you'd expect after defining it, you get an error message like, "Cannot guess decreasing argument of fix." What is this nonsense? 
  
  Alas, there is hope! Coq, being aware it's a terrible guesser, allows you to provide your own proof that a fixpoint function won't loop forever.
  
  Alas, there is despare. There seems to be but one resource to help you on your self defining journey-- The General Recursion chapter of Certified Programming with Dependent Types (http://adam.chlipala.net/cpdt/html/GeneralRec.html), and if you're anything like me in height it will go way over your head. I will say, however, that without this chapter I would have never figured this stuff out. As complicated as it is, it is infinitely better than just looking at the Coq libraries. I was able to get just enough from it to struggle my way through over the course of.. well a long time. I could find nowhere on the internet a step by step guide or tutorial on how to define my own fixpoint function with proof of well founded-ness--something I thought surely I was not the first person to want to do. "Whence" this blog post. 
  
  Alas, ther is hope! Below I will go through how to define the "intuitive" definition of integer division (which is non-terminating as far as Coq can tell) as an example. Perhaps you can use this as a template to define your own more complex, non-trivial well-founded recursive functions!
  ** Division
  Suppose you want to define integer division in Coq--innocent enough. For the sake of simplicity, let's say dividing by zero is zero. You can prevent this of course, but for the sake of 'that's-not-what-I'm-getting-at' let's just say it's zero. You might then come up with a definition like the following:
<<
  Fixpoint divide (x y : nat) : nat :=
   match (x,y) with
    | (0, _) => 0
    | (_, 0) => 0
    | (_, _) => if (Nat.leb y x) 
             then S (divide (x -y) y)
             else 0
   end. 
>>
To which Coq replies, "Error: Cannot guess decreasing argument of fix."
        *)
(*
Fixpoint divide (x y : nat) : nat :=
   match (x,y) with
    | ( 0, _) => 0
    | ( _, 0) => 0
    | (_,_) => if (Nat.leb y x) 
             then S (divide (x -y) y)
             else 0
   end.
*)
(** 
Here's what we're going to do:

In order to define this recursive function, we need to prove that each recursive call
is given a 'smaller' argument. Whenever you define a fixpoint and all the recursive calls are on _subterms_ of the argument, Coq can figure out the function is decreasing on its own. For example,
*)
Fixpoint f (n : nat) : nat :=
 match n with
 | O => 0
 | S n' => f n' 
end.

(** is perfectly easy to define since every recursive call to _f_ is given a subterm of the current argument. 

While you and I know that our definition of divide is called on "smaller and smaller" terms, Coq doesn't know this on its own. We're not recursively calling _divide_ on any subterms of x or y. 

Don't worry! We can fix this problem on our own. Let's look at the
actual Definition of Fix so we can make one ourselves. *)
Check Fix.
(**
<<
Fix
     : forall (A : Type) (R : A -> A -> Prop),
       well_founded R ->
       forall P : A -> Type,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, P x
>>
What is this well_founded thing? What is this 'R'? What is anything? WELL, well_founded-ness is how Coq proves to itself that this function will eventually end. Thereby, making it legal in its calculus of constructive logic (no infinite regression!). It looks pretty icky because it is. Nevertheless we'll get through it piece by piece.

  
  The relation 'R' is a
relation that is an "is less than" relation. Of course, any old relation
could have the type 'A -> A -> Prop', but only one that defines this 
monotonic decreasing behavior will be able to satisfy the 
'well_founded R' construction as required by Fix.  

Let's now go down the rabbit hole a little further and look at the definition
of well_founded. 

*) 
Print well_founded.

(**
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
*)
Print Acc.
(** 
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
Proof. intros.  induction x. apply zeroAccssible.
constructor.
intros. destruct y. apply zeroAccssible. inversion H. subst. assumption. subst.
destruct IHx. constructor. apply H0. auto.
Qed.
Print well_founded.
(* 
  1. do induction on the thing.
  2. prove the base case.
  3. constructor. intros.  
  4. destruct on the thing that is less than the other thing. 
  5. you should have the base case to prove again.
  6. invert on H, the less than relation. subst. you should have that assumption.
  7. subst. destruct on your inductive hypothesis.
  8. constructor. apply your new result from inducting on hypo. auto.
*)
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
Require Nat.

(*
Fixpoint divide (x y : nat) : nat :=
  if (Nat.leb y x) then S (divide (x -y) y)
   else 0.  
*)
Inductive MyStupidPair : Type :=
 | mystupidpair : nat -> nat -> MyStupidPair. 

(*
Fixpoint divide2 (p : MyStupidPair) : nat :=
 match p with
  | mystupidpair _ 0 => 0
  | mystupidpair x y => S (divide2 (mystupidpair (x -y) y))
 end.
 *) 
Definition first_ltR (p1 p2 : MyStupidPair) : Prop := 
 match (p1,p2) with
 | (mystupidpair p1x _, mystupidpair p2x _) => lt p1x p2x
end.
Check first_ltR.


Theorem helper : forall x y z, Acc first_ltR (mystupidpair x y) -> Acc first_ltR (mystupidpair x z).
Proof. intro. induction x. intros. constructor. intros. destruct y0. inversion H0.
intros. destruct H.   constructor. intros. apply H. destruct y0. destruct n.
unfold first_ltR. auto.
  
inversion H0. subst. unfold first_ltR. auto. subst. unfold first_ltR in H0.
unfold first_ltR. assumption. 
Defined. 
(* 
  1. do induction on the thing.
  2. prove the base case.
  3. constructor. intros.  
  4. destruct on the thing that is less than the other thing. 
  5. you should have the base case to prove again.
  6. invert on H, the less than relation. subst. you should have that assumption.
  7. subst. destruct on your inductive hypothesis.
  8. constructor. apply your new result from inducting on hypo. auto.
*)
Theorem allPairs_Acc : forall p : MyStupidPair, Acc first_ltR p.
Proof. intro. destruct p.  induction n.
(*base case *)
constructor. intros. unfold first_ltR in H. destruct y. inversion H.
(* end base case *)      
constructor. intros (* step 3 *).  
(*step 4 *) destruct y. destruct n1.
(*base case again *)
constructor. intros. unfold first_ltR in H0. destruct y. inversion H0. 
(* end base case again *)
inversion H. subst. apply helper with (z:=n2) in IHn.  assumption (*6*).
(*7*) subst. destruct IHn.
(*8*) constructor. apply H0. auto.
Defined.
 

Theorem pairsWfr : well_founded first_ltR.
Proof. constructor. apply allPairs_Acc. Defined. (*This must be Defined! *)
  
Definition divide : MyStupidPair -> nat.
 refine 
   (Fix pairsWfr (fun _ => nat)
      (fun (p : MyStupidPair)
        (subcall : forall  p' : MyStupidPair, first_ltR p' p -> nat) =>
        match p with
          | mystupidpair x 0 => 0
          | mystupidpair x y =>  
              if (Nat.leb y x) then S (subcall (mystupidpair (x -y) y) _ )
                               else 0
        end

         )
            ). (*coq too stupid to realize I can't have zero case here. *) Abort.
            
            (*Require Import Omega.*)
            
Lemma ltSucc : forall x y, x < y -> x < S y.
intro. induction x. auto. intros. destruct y. auto. auto. Defined.

Theorem natsub : forall n x, n - x < S n.
Proof. intro. induction n. simpl. intro. auto.
intros. simpl. destruct x. auto. eapply ltSucc in IHn. apply IHn. Defined.

Require Import Omega.

Definition divide_v2 : MyStupidPair -> nat.
 refine 
   (Fix pairsWfr (fun _ => nat)
      (fun (p : MyStupidPair)
        (subcall : forall  p' : MyStupidPair, first_ltR p' p -> nat) =>
        _

         )
            ). destruct p. destruct n0. 
             (*divide by zero case *)
             exact 0.
             (* S n0 case *)
             destruct (Nat.leb (S n0) n) eqn :case.
               (*we can keep dividing! *) refine  
                (S (subcall (mystupidpair (n - (S n0)) (S n0))  _) ). 
                unfold first_ltR. destruct n. inversion case.
                simpl in case. simpl. 
                 apply natsub. 
                (*omega.*)
                 
                (* we are done dividing, i.e. (S n0) is not less than n *) 
                exact 0. Defined.
Print divide_v2. 
Definition myDivide (x y : nat) := divide_v2 (mystupidpair x y).
   

(*ANY PROOF involved in defining the function must be defined not qed. *)
Eval compute in (myDivide 0 0).
Eval cbn in (myDivide 3 4).
Eval compute in (myDivide 4 2).
Eval compute in (myDivide 5 2).
Eval compute in (myDivide 100 7).
Eval compute in (myDivide 3 4).

