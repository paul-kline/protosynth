(** * Intro
  So you've run into despare.. You want to define a fixpoint (recursive) function in Coq, but instead of the beautiful green line you'd expect after defining it, you get an error message like, "Cannot guess decreasing argument of fix." What is this nonsense? 
  
  Alas, there is hope! Coq, being aware it's a terrible guesser, allows you to provide your own proof that a fixpoint function won't loop forever.
  
  Alas, there is despare. There seems to be but one resource to help you on your self defining journey-- The General Recursion chapter of Certified Programming with Dependent Types (http://adam.chlipala.net/cpdt/html/GeneralRec.html), and if you're anything like me in height it will go way over your head. I will say, however, that without this chapter I would have never figured this stuff out. As complicated as it is, it is infinitely better than just looking at the Coq libraries. I was able to get just enough from it to struggle my way through over the course of.. well a long time. I could find nowhere on the internet a step by step guide or tutorial on how to define my own fixpoint function with proof of well founded-ness--something I thought surely I was not the first person to want to do. "Whence" this blog post. 
  
  Alas, ther is hope! Below I will go through how to define the "intuitive" definition of integer division (which is non-terminating as far as Coq can tell) as an example. Perhaps you can use this as a template to define your own more complex, non-trivial well-founded recursive functions!
  ** Division
  Suppose you want to define integer division in Coq--innocent enough. For the sake of simplicity, let's say dividing by zero is zero. You can prevent this of course, but for the sake of 'that's-not-what-I'm-getting-at' let's just say it's zero. You might then come up with a definition like the following ('n' stands for numerator, 'd' for denominaor):
<<
  Fixpoint divide (n d : nat) : nat :=
   match (n,d) with
    | (0, _) => 0
    | (_, 0) => 0
    | (_, _) => if (Nat.leb d n) 
             then S (divide (n - d) d)
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

(** is perfectly easy to define since every recursive call to _f_ is given a subterm of the current argument. Thereby always getting smaller. 

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
Well that's pretty confusing. What is this well_founded thing? What is this 'R'? What is anything? Let's ignore everything else and focus on the well_founded part. For now, just know that we need to provide this well_founded _thing_ so we might as well explore that first. We'll get back to what all that other messy stuff is later.

 Well_founded-ness is how Coq proves to itself that this function will eventually end. Thereby, making it legal in its calculus of constructive logic (no infinite regression!). It looks pretty icky because it is. Nevertheless we'll get through it piece by piece.

  

Let's go down the rabbit hole a little further and look at the definition of well_founded. 

 *)  
Print well_founded. 
(**
well_founded = 
fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
     : forall A : Type, (A -> A -> Prop) -> Prop

The definition of well_founded is much better to look at with parens like this:
<<
well_founded = 
fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
     : (forall A : Type, (A -> A -> Prop) ) -> Prop
>>
Argument A is implicit

Now you can see that the big mess is just telling you what the type of 'Acc R a' must be.

As an aside, remember 'Argument A is implicit' means we don't actually have to provide that argument. Coq is smart enough (for once) to figure it out from the types provided in the R relation. 

Ahh, the 'R' relation; I'm glad you mentioned it. The relation 'R' is a relation that is a "less than" relation. How would you know that it has to be a "less than" relation as opposed to any other and how this "less-than-ness" enforced? You wouldn't know that yet, but I do. You will soon realize that the definition of Acc (which we'll get to soon) forces this relation into an "is less than" shape. I keep putting "less than" in quotes because that's what makes sense to me. It's really more of a "the first argument is closer to a terminating term than the second" relation. In our case with division, we terminate when y is zero, OR when x < y and we can't do integer division any further. In our case we need to prove that every subcall of divide is called with an x that is less than the one handed to the current iteration.   Only a relation that defines this monotonic decreasing behavior will be able to satisfy the constructor of Acc. 

Let's get back to well_founded for a minute before we move on to Acc. <<
well_founded = 
fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
     : (forall A : Type, (A -> A -> Prop) ) -> Prop
>>
What does well_founded say in people-speak? You try first.

 'well_founded' is a function that takes a relation 'R' and gives you back another function. Namely this:
 <<
(  forall a : A, Acc R a
     : forall A : Type, (A -> A -> Prop) -> Prop). 
>>
THIS function takes a proof of type: <<
 forall a : A, Acc R a >> and spits out a Prop. 
>>

'Acc' stands for 'Accessibility'.

Here's a really important sentence:

Basically, a relation 'R' over the domain 'A' is well founded IF you can prove that _every_ element in 'A' is Accessible (Acc R a).

Okay, let's look at Acc. *)

Print Acc.
(** <<
Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x
>>
Holy crap it's an inductive type. Finally, we are looking at something that in its definition doesn't introduce something we haven't seen before! What does Acc say in English? Give it a go, and I will too. 

Acc is an inductive type of type Prop ( Acc .... : Prop).
It is 'indexed' over an 'A' which has type 'Type', a relation 'R' (which we've talked about), and a particular thing (_x_) of type A. To make an Acc there is only one constructor, 'Acc_intro' which must be provided with a proof that for any element 'y' that is "less than" x (R y x), it's 
accessible (Acc R y). If you can provide that, then x is accessible as well (Acc R x). 
And that's it! Now that we've explored all the way to the bottom of the chain we can start building our way back up to Fix.
So, let's start with 'R'. the 'A' type in R is the type of the argument that we must prove decreases.

Something may have been bothering you up to this point. We keep talking about "the argument" to the function being "less than" each time. What about functions that take more than one argument? Worse yet, what if you need all of those arguments to determine if you're closer to a termination term? 

There may be more solutions than this, but I just like to make a wrapper to hold everything I need. In our example, divide takes two naturals. So I make a wrapper for the 2 naturals into one type: *)
Inductive MyStupidPair : Type :=
 | mystupidpair : nat -> nat -> MyStupidPair. 

(** 
I may have voiced my frustration with this bookkeeping step in the naming.

'MyStupidPair' will play the role of 'A'. 

What is our "less than" relation? Well let's look at what our divide function would look like with this new wrapper thing:
<<
Fixpoint divide2 (p : MyStupidPair) : nat :=
 match p with
  | mystupidpair _ 0 => 0
  | mystupidpair n d => S (divide2 (mystupidpair (n -d) d))
 end. 
>>
All we care about is that the first number 'n' is smaller each time. In whatever function you're trying to define, your "less than" relation probably depends on all the arguments, but we only care about one of ours. So our less than relation would look something like:
 *) 
Definition first_ltR (p1 p2 : MyStupidPair) : Prop := 
 match (p1,p2) with
  | (mystupidpair n1 _, mystupidpair n2 _) => n1 < n2
  end.
Check first_ltR.
(** 
Looks good. Now what? Well we know for well_founded we need a proof that every element of MyStupidPair is Accessible. Let's start there.

Let's start with the base case.

*)
Theorem smallestPairAccessible : forall d, Acc first_ltR (mystupidpair 0 d).
Proof. 
constructor. intros. unfold first_ltR in H. destruct y. inversion H.
Defined.
(**
Cool. Let's pretend I got that proof right away. 

I also have a very important note to share with you that isn't relevant until later, but you see it now, so I should explain it now. I said <<Defined>> and not <Qed>. This is an absolute must. Remember our end goal is defining a function. This proof (and any proof that uses this proof will in one way or another be passed to Fix as an argument in the well_founded proof. When you write a theorem or whatever and end it with <<Qed>> Coq forgets about how you got to the end, and just remembers that you got there legally. We are proving things for the purpose of construction. Therefore we need Coq to 'remember' how we got there. If we leave any proof as <<Qed>> instead of <<Defined>> your final function will not reduce past (Fix_F <<huge-mess-of-crap>>) (args..). Coq can't evaluate the proofs because it has forgotten how. This also unfortunately means you can't use proofs in the standard library that end in <<Qed>>.

Note: You also can't use omega anywhere. This currently causes Coqtop to "die badly" when you try to use the final function. This seems like a bug and has been reported.

Anyway, let's prove that all elements of MyStupidPair are accessible. 
*) 
 
Theorem allPairs_Acc_getStuck : forall p : MyStupidPair, Acc first_ltR p.
Proof. intro. destruct p.  induction n.
(*base case *)
apply smallestPairAccessible.
(* end base case *)      
constructor. intros (* step 3 *).  
(*step 4 *) destruct y. destruct n1.
(*base case again *)
constructor. intros. unfold first_ltR in H0. destruct y. inversion H0. 
(* end base case again *)
inversion H. subst. Abort.
(**
I got stuck here:
<<
n0, n1, n2 : nat
IHn : Acc first_ltR (mystupidpair (S n1) n0)
H : first_ltR (mystupidpair (S n1) n2) (mystupidpair (S (S n1)) n0)
______________________________________(1/2)
Acc first_ltR (mystupidpair (S n1) n2)
>>

My induction hypothesis is specifically for n0, but I need it for n2! Obviously, in my relation the second number in the pair doesn't matter, but I need that proof.  
*)
Theorem wellOfCourseThisisTrue : forall x y z, Acc first_ltR (mystupidpair x y) -> Acc first_ltR (mystupidpair x z).
Proof. intro. induction x. intros. constructor. intros. destruct y0. inversion H0.
intros. destruct H.   constructor. intros. apply H. destruct y0. destruct n.
unfold first_ltR. auto.
  
inversion H0. subst. unfold first_ltR. auto. subst. unfold first_ltR in H0.
unfold first_ltR. assumption. 
Defined.
(**
Let's pretend this proof I got straight away as well. (Note <<Defined>>!)

Now let's try that again. *)

Theorem allPairs_Acc : forall p : MyStupidPair, Acc first_ltR p.
Proof. intro. destruct p.  induction n.
(*base case *)
apply smallestPairAccessible. 
(* end base case *)      
constructor. intros (* step 3 *).  
(*step 4 *) destruct y. destruct n1.
(*base case again *)
constructor. intros. unfold first_ltR in H0. destruct y. inversion H0. 
(* end base case again *)
inversion H. subst. apply wellOfCourseThisisTrue with (z:=n2) in IHn.  assumption (*6*).
(*7*) subst. destruct IHn.
(*8*) constructor. apply H0. auto.
Defined.

(**
As always, let's pretend I got this proof straight away. 
A word of caution however: While proving the accessibility of all elements in your domain, it is _really_ easy to find yourself with an impossible proof goal. In fact, proving this all Accessible theorem is why I was stuck on well_founded-ness for so long. I eventually figured it out and have created these steps to follow to stay on the path of righteousness. Feel free to ignore them at first and try to prove your all accessible theorem on your own. You may very well succeed, but I always got tempted to apply something that led me to an impossible proof goal and applied it. 
<<
  1. do induction on the thing you're proving is accessible.
  2. prove the base case.
  3. constructor. intros.  
  4. destruct on the thing that is less than the other thing. 
  5. you should have the base case to prove again or something very close to it.
  6. invert on H, the less than relation. subst. you should have that assumption.
  7. subst. destruct on your inductive hypothesis.
  8. constructor. apply your new result from inducting on hypo. auto.
>>

We pretty much have well_founded-ness for our relation now. We can start crawling out of the rabbit hole.
*)

Theorem pairsWfr : well_founded first_ltR.
Proof. constructor. apply allPairs_Acc. Defined.
(** 
  That was nice. Now we've got what we need. But let's look <<Fix>> again.
  *)
Print Fix.
(**
<<
Fix = 
fun (A : Type) (R : A -> A -> Prop) (Rwf : well_founded R) (P : A -> Type)
  (F : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A) => 
Fix_F P F (Rwf x)
     : forall (A : Type) (R : A -> A -> Prop),
       well_founded R ->
       forall P : A -> Type,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, P x

Arguments A, R are implicit
>>
Cool. A and R are implicit, we also might as well look at this for our specific example as well:<<

Fix = 
fun (Rwf : well_founded first_ltR) (P : A -> Type)
  (F : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A) => 
Fix_F P F (Rwf x) : well_founded first_ltR ->
       forall P : A -> Type,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, P x
>> 
That helps a little I guess, but heck, it's still pretty confusing. 
*)
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
            ). (** coq too stupid to realize I can't have zero case here. *) Abort.
            
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
                (* omega.*)

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