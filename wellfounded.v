(** * Intro
  So you've run into despare.. You want to define a fixpoint (recursive) function in Coq, but instead of the beautiful green line you'd expect after defining it, you get an error message like, <<"Cannot guess decreasing argument of fix.">> What is this nonsense? 
  
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

While you and I know that our definition of divide is called on "smaller and smaller" terms, Coq's too dumb to see it. We're not recursively calling _divide_ on any subterms of x or y. 

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
(** <<
well_founded = 
fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
     : forall A : Type, (A -> A -> Prop) -> Prop
>>
The definition of well_founded is much better to look at with parens like this:
<<
well_founded = 
fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
     : (forall A : Type, (A -> A -> Prop) ) -> Prop

Argument A is implicit
>>
Now you can see that the big mess is just telling you what the type of <<Acc R a>> must be.

As an aside, remember 'Argument A is implicit' means we don't actually have to provide that argument. Coq is smart enough (for once) to figure it out from the types provided in the R relation. 

Ahh, the 'R' relation; I'm glad you mentioned it. The relation 'R' is a relation that is a "less than" relation. How would you know that it has to be a "less than" relation as opposed to any other and how this "less-than-ness" enforced? You wouldn't know that yet, but I do. You will soon realize that the definition of Acc forces this relation into an "is less than" shape. I keep putting "less than" in quotes because that's what makes sense to me. It's really more of a "the first argument is closer to a terminating term than the second" relation. In our case with division, we terminate when d is zero, OR when n < d and we can't do integer division any further. We must prove that every subcall of divide is called with an x that is less than the one handed to the current iteration.   Only a relation that defines this monotonic decreasing behavior will be able to satisfy the constructor of Acc. It's all quite clever. 

Let's get back to well_founded for a minute before we move on to Acc. 
<<
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

A relation 'R' over the domain 'A' is well founded IF you can prove that _every_ element in 'A' is Accessible (Acc R a).

Okay, let's look at Acc. *)

Print Acc.
(** <<
Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x
>>
Holy crap it's an inductive type. Finally, we are looking at something that in its definition doesn't introduce something we haven't seen before! What does Acc say in English? Give it a go, and I will too. 

Acc is an inductive type of type Prop.
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

'MyStupidPair' will play the role of 'A', the domain of our fixpoint function.

What is our "less than" relation? Well let's look at what our divide function would look like with this new wrapper thing:
<<
Fixpoint divide2 (p : MyStupidPair) : nat :=
 match p with
  | mystupidpair 0 _ => 0
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

I also have a very important note to share with you that isn't relevant until later, but you see it now, so I should explain it now. I said <<Defined>> and not <<Qed>>. This is an absolute must. Remember our end goal is defining a function. This proof (and any proof that uses this proof will in one way or another be passed to Fix as an argument in the well_founded proof. When you write a theorem or whatever and end it with <<Qed>> Coq forgets about how you got to the end, and just remembers that you got there legally. We are proving things for the purpose of construction. Therefore we need Coq to 'remember' how we got there. If we leave any proof as <<Qed>> instead of <<Defined>> your final function will not reduce past (Fix_F <<huge-mess-of-crap>>) (args..). Coq can't evaluate the proofs because it has forgotten how. This also unfortunately means you can't use proofs in the standard library that end in <<Qed>>.

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
Let's pretend this proof I got straight away as well. (Note: <<Defined>>!)

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
A word of caution however: While proving the accessibility of all elements in your domain, it is _really_ easy to find yourself with an impossible proof goal. In fact, proving this all Accessible theorem is why I was stuck on well_founded-ness for so long. After I figured it out I created these steps to follow to stay on the path of righteousness. Feel free to ignore them at first and try to prove your accessibility theorem on your own. You may very well succeed, but I always got tempted to apply something that led me to an impossible proof goal and applied it. 
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
  That was nice. Now we've got what we need. Let's look at <<Fix>> again.
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
Cool. Very confusing. A and R are implicit at least.  Let's look at this type with our specific example:

<<
Fix = 
fun (Rwf : well_founded first_ltR) (P : A -> Type)
  (F : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A) => 
Fix_F P F (Rwf x) : well_founded first_ltR ->
       forall P : A -> Type,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, P x
>>
 
That helps a little I guess, but holy crap, it's still pretty confusing. 


Fix is a function that takes the well_founded proof we've been working on. It also takes this <<P>> function that's from <<A>> to <<Type>>. Why? Well I'll tell you! Coq functions can be dependently typed, remember? In our case of division, we always return something that's a <<nat>>. But that doesn't have to be the case. P is how you specify how the type of the input affects the type of the output. Our divide function is not dependently typed, so for us the P function is as simple as:
<< (fun _ => nat) >>
For every input, the return type is nat.

Cool. Next!
<<
(F : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A) => 
Fix_F P F (Rwf x) : well_founded first_ltR ->
       forall P : A -> Type,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, P x
>>

Let's ignore everything after the << => >>. That's the type of the final fixpoint we're going to get. So let's focus on the left side of => on the stuff we need to provide. 
<<
(F : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A) => 
>>

We must give an F. 

F is a function whose type starts with << forall x : A >>. For functions, this just means it accepts something of type 'A' as a parameter named 'x'. The second parameter of F is.. by golly, another function. A function of type <<
(forall y : A, R y x -> P y)
>>
This function takes something else of type A (named y), a proof that y is "less than" x, and gives you back the proper type according to our type function P. 

What's going on here? What is this second function supposed to be? Think about it first.


It is the recursive call. Take a look at that type again with this in mind. 
<<
F takes:
   1. (x : A).
   2. a function that is good for all elements "less than" x.
     (You have to provide the proof that y, the argument passed 
     to this second function is "less than" x  to use this function!
     It will look something like:
         f' (y : A) (prf : R y x) : (P y) 
     ) 
     >> 
     
That's the secret. That's the proof of termination. _To even use_ the recursive function, you have to provide proof that you're calling the function on an argument closer to termination than the previous argument was.
AAAAAAAAAAAAAAND.... since you've already proven that every element is accessible (the constructor of well_founded), we've proven that it's impossible for this function to iterate forever. How? Yeah, the function is getting called on smaller and smaller things, but how do we know  it will ever end?? After all, think about real numbers. Let's say our terminating case is zero. You give me any positive real number, and I can give you a real number that's smaller than that but still not zero.
 
 <<
   You: 0.000000000000001
   Me : 0.0000000000000001
   
   You: 0.000000000000000000000001
   Me:  0.0000000000000000000000001
   >>

   You get the idea. We could do this all day (life). Give up. In fact, I could give you an infinite number of numbers less than yours. The point is, just because our recursive argument is getting smaller every iteration doesn't necessarily mean that it will ever reach a stopping point. 
   
   That's why we proved the accessibility of every element in our domain. We've proven that for every element in the domain A, it's accessible. And do you remember how to prove a particular element is accessible? You have to prove that all elements less than it are also accessible. This is an impossible proof for the real numbers. There is no concept of "the next" or "the previous" real number. Okay, so zero is your base case, but then what? For each real number (of which they are uncountably infinite) There are uncountably infinte proofs you must provide. The case with naturals, however, is once you give me a particular natural, there are a finite number of naturals between that number and zero. You won't be taking steps forever. The accessibility of every element (well founded-ness) ensures that.  

Enough talk, let's see it.
*)

Definition divide : MyStupidPair -> nat.
 refine 
   (Fix pairsWfr (fun _ => nat)
      (fun (p : MyStupidPair)
        (subcall : forall  p' : MyStupidPair, first_ltR p' p -> nat) =>
        match p with
          | mystupidpair n 0 => 0
          | mystupidpair n d  =>  
              if (Nat.leb d n) then S (subcall (mystupidpair (n -d) d) _ )
                               else 0 
        end

         )
            ). Abort.
(** Crap.. You and I know that when I enter the prover to fill in the '_', it's impossible for d to be zero because of the previous match case. However Coq as of version 8.5pl2 has no idea this is the case. Instead we'll just have to encode the whole dang function body in the prover. 
*)
Definition divide_v2 : MyStupidPair -> nat.
 refine 
   (Fix pairsWfr (fun _ => nat)
      (fun (p : MyStupidPair)
        (subcall : forall  p' : MyStupidPair, first_ltR p' p -> nat) =>
        _

         )
            ). destruct p. destruct n0. 
             idtac "divide by zero case".
             exact 0.
            idtac "S n0 case". 
             destruct (Nat.leb (S n0) n) eqn :case.
               idtac "we can keep dividing!". refine  
                (S (subcall (mystupidpair (n - (S n0)) (S n0))  _) ). 
                unfold first_ltR. destruct n. inversion case.
                simpl in case. simpl. 
(** Allow me to interupt. Our proof state is
<<
n, n0 : nat
subcall : forall p' : MyStupidPair, first_ltR p' (mystupidpair (S n) (S n0)) -> nat
case : Nat.leb n0 n = true
______________________________________(1/2)
n - n0 < S n
>>

You may be tempted to use some theorems from the standard library for this. Don't give in. Remember your function won't simplify if you use anything declared with <<Qed>> instead of <<Defined>>.  

NOTE: omega will solve this goal, but uses lemmas defined with Qed. Which we can't use here.  *)
Require Import Omega. 
    Lemma natsub : forall n x, n - x < S n.
    Proof. intro.  induction n. auto.
    intros. simpl. destruct x. auto.  
        Lemma ltSucc : forall x y, x < y -> x < S y.
        auto. 
        Defined.
    eapply ltSucc in IHn. apply IHn. 
    Defined.
 omega.
 (*              apply natsub.*)
                idtac "we are done dividing, i.e.S n0 is not less than n". 
                exact 0. Defined.

(** WE DID IT *)
Print divide_v2.

(** THAT'S SO UGLY. And beautiful.
If I put the output here it would double the length of this post. 

I don't want to have to make a MyStupidPair every time I want to divide.
*)
Definition myDivide (x y : nat) := divide_v2 (mystupidpair x y).
Check myDivide. 
(** <<
myDivide
     : nat -> nat -> nat
>>
It's beautiful. 
*)
Eval compute in (myDivide 0 0).
Eval cbn in (myDivide 3 4).
Eval compute in (myDivide 4 2).
Eval compute in (myDivide 5 2).
Eval compute in (myDivide 1000 7).
Eval compute in (myDivide 3 4).

(** The end *)
