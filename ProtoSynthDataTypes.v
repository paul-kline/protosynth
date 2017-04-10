Add LoadPath "/users/paulkline/Documents/coqs/protosynth".
Add LoadPath "/home/paul/Documents/coqs/protosynth/cpdt/src" as Cpdt.  
Require Import MyShortHand.

Inductive Noun : Set:=
  | VirusChecker
  | PCR.
Theorem eq_dec_Noun : equality Noun.
crush_equal. 
Defined. 
Hint Resolve eq_dec_Noun : eq_dec_db. 
(* Now we define what it is we would like to know about these nouns. *)
Inductive Attribute : Set :=
  | Name : Attribute
  | Hash : Attribute
  | Index : nat -> Attribute
  | Version : Attribute.
Theorem eq_dec_Attribute : equality Attribute. 
crush_equal. Defined. 
Hint Resolve eq_dec_Attribute : eq_dec_db. 
(*We only want to disallow nonsensical combinations, like a (PCR, version),
 hence this relation. *)
Inductive DescriptionR : Noun -> Attribute -> Set :=
  | pcrMR : forall n, DescriptionR PCR (Index n)
  | virusCheckerNameR : DescriptionR VirusChecker Name
  | virusCheckerVersionR : DescriptionR VirusChecker Version.
Theorem eq_dec_DescriptionR {n} {a}:  equality (DescriptionR n a).
crush_equal. 
Defined.
Hint Resolve eq_dec_DescriptionR : eq_dec_db.  
Hint Resolve eq_dec_DescriptionR.
 
(* This 'extra step' is done simply so that comparison between descriptors
is 'easy.'It is much more involved to be able to compare indexed types. *)
Inductive Description : Set :=
  | descriptor {n : Noun} {a : Attribute} : DescriptionR n a -> Description.
Theorem eq_dec_Description : equality Description.
crush_equal. 
Defined.
Hint Resolve eq_dec_Description : eq_dec_db. 

(*This defines what the type of measuring these things should be. *)
Definition measurementDenote (d: Description) :=
match d with
 | descriptor r => (match r with
    | pcrMR n => nat
    | virusCheckerNameR => nat
    | virusCheckerVersionR => nat
    end)
end.

(* Here we begin specificiation of requirements. So not only do I want a particular measurment,
   but I want it to be certain values. *) 
Inductive Requirement (d : Description) :=
| requirement : ( (measurementDenote d) -> bool) -> Requirement d.
Require Import FunctionalExtensionality. 
Theorem eq_dec_f {A} {B} : forall (a b : (A -> B)), a =<> b.
Proof. intros.
specialize functional_extensionality with a b. intros.
 Admitted.
Hint Resolve eq_dec_f : eq_dec_db. 
Theorem eq_dec_Requirement : forall d (x y : Requirement d), x =<> y.
Proof. intros. 
destruct d. 
destruct d; 
crush_equal. 
Defined. 
Hint Resolve eq_dec_Requirement : eq_dec_db.



(* This begins the defining of what a privacy policy is. First we define a rule.
    A rule regulates the release of a measurement. We could decide to release information if
    some counter condition holds; we could release it for free; we could explicitly never release it; 
    or some combination of and-ing and or-ing rules.
    Note that at this point we've allowed for nonsensical release rules like, "never release or release for free",
     "release for free and never release".
    NOTE: If we can't request something twice, what if duplicate occurs in rule req?
          todo: keep all received measurements and check those first for the value *) 
Inductive Rule (mything : Description) :=  
| rule  {your : Description} : (Requirement your) -> Rule mything
| free : Rule mything
| never : Rule mything.
(*| multiReqAnd : Rule mything ->Rule mything -> Rule mything
| multiReqOr : Rule mything -> Rule mything -> Rule mything.
*)
Theorem eq_dec_Rule : forall x, equality (Rule x).
Proof.   


intros. intro_equals. 
destruct x.  
destruct d;
generalize dependent x0; 
induction y;
intro_equals; 
destruct x0; try first [decidable |  
crush_equal].
(* rest is for and and or case included *)
(*
specialize IHy1 with x0_1. 
specialize IHy2 with x0_2.
destruct IHy1.  subst. 
destruct IHy2.  subst. decidable. 
decidable.  decidable.
specialize IHy1 with x0_1. 
specialize IHy2 with x0_2.
destruct IHy1.  subst. 
destruct IHy2.  subst. decidable.
crush_equal. decidable.
specialize IHy1 with x0_1. 
specialize IHy2 with x0_2.
destruct IHy1.  subst. 
destruct IHy2.  subst. decidable. 
decidable.  decidable.
specialize IHy1 with x0_1. 
specialize IHy2 with x0_2.
destruct IHy1.  subst. 
destruct IHy2.  subst. decidable.
crush_equal. decidable.

specialize IHy1 with x0_1. 
specialize IHy2 with x0_2.
destruct IHy1.  subst. 
destruct IHy2.  subst. decidable. 
decidable.  decidable.
specialize IHy1 with x0_1. 
specialize IHy2 with x0_2.
destruct IHy1.  subst. 
destruct IHy2.  subst. decidable.
crush_equal. decidable.
*)
Defined.
Hint Resolve eq_dec_Rule : eq_dec_db. 
(* simply a list of rules. *)
Inductive PrivacyPolicy :=
| EmptyPolicy : PrivacyPolicy
| ConsPolicy {d :Description}: 
    Rule d -> 
    PrivacyPolicy -> PrivacyPolicy.
Theorem eq_dec_PrivacyPolicy : equality PrivacyPolicy.
intro_equals.
generalize dependent x. 
induction y; try
crush_equal + decidable.
intros. destruct x; decidable.
intros. destruct x. decidable. 
 specialize IHy with x.
 destruct IHy.  subst. crush_equal.  
 crush_equal.
Defined.
Hint Resolve eq_dec_PrivacyPolicy : eq_dec_db. 
Inductive Action : Set :=
 | ASend : Action
 | AReceive : Action.
Theorem eq_dec_Action : equality Action. 
crush_equal. 
Defined.
Hint Resolve eq_dec_Action : eq_dec_db. 
(*A RequestItem is used to compose a list of the items and requirements upon 
those items in an attestation *)
Inductive RequestItem : Set :=
 | requestItem (d : Description) : (Requirement d) -> RequestItem.
Theorem eq_dec_RequestItem : equality RequestItem.
intro_equals.
generalize dependent x.
induction y;  intros. destruct x; try crush_equal.
Defined.
Hint Resolve eq_dec_RequestItem : eq_dec_db.
 
Inductive RequestLS : Set :=
 | emptyRequestLS : RequestLS
 | ConsRequestLS : RequestItem -> RequestLS -> RequestLS.
Theorem eq_dec_RequestLS : equality RequestLS.
crush_equal. 
Defined.
Hint Resolve eq_dec_RequestLS : eq_dec_db.   

Inductive Role : Set :=
 | Appraiser
 | Attester.
Theorem eq_dec_Role : equality Role. 
crush_equal. 
Defined. 
