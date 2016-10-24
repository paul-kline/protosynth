Add LoadPath "/users/paulkline/Documents/coqs/protosynth". 
Require Import MyShortHand.

Inductive Noun : Set:=
  | VirusChecker
  | PCR.

(* Now we define what it is we would like to know about these nouns. *)
Inductive Attribute : Set :=
  | Name : Attribute
  | Hash : Attribute
  | Index : nat -> Attribute
  | Version : Attribute.

(*We only want to disallow nonsensical combinations, like a (PCR, version),
 hence this relation. *)
Inductive DescriptionR : Noun -> Attribute -> Set :=
  | pcrMR : forall n, DescriptionR PCR (Index n)
  | virusCheckerNameR : DescriptionR VirusChecker Name
  | virusCheckerVersionR : DescriptionR VirusChecker Version.

(* This 'extra step' is done simply so that comparison between descriptors
is 'easy.'It is much more involved to be able to compare indexed types. *)
Inductive Description : Set :=
  | descriptor {n : Noun} {a : Attribute} : DescriptionR n a -> Description.


(*This defines what the type of measuring these things should be. *)
Definition measurementDenote (d: Description) :=
match d with
 | descriptor r => (match r with
    | pcrMR n => nat
    | virusCheckerNameR => nat
    | virusCheckerVersionR => bool
    end)
end.

(* Here we begin specificiation of requirements. So not only do I want a particular measurment,
   but I want it to be certain values. *) 
Inductive Requirement (d : Description) :=
| requirement : ( (measurementDenote d) -> bool) -> Requirement d.


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
| never : Rule mything
| multiReqAnd : Rule mything ->Rule mything -> Rule mything
| multiReqOr : Rule mything -> Rule mything -> Rule mything.

(* simply a list of rules. *)
Inductive PrivacyPolicy :=
| EmptyPolicy : PrivacyPolicy
| ConsPolicy {d :Description}: 
    Rule d -> 
    PrivacyPolicy -> PrivacyPolicy.

Inductive Action : Set :=
 | ASend : Action
 | AReceive : Action.

(*A RequestItem is used to compose a list of the items and requirements upon 
those items in an attestation *)
Inductive RequestItem : Set :=
 | requestItem (d : Description) : (Requirement d) -> RequestItem.

Inductive RequestLS : Set :=
 | emptyRequestLS : RequestLS
 | ConsRequestLS : RequestItem -> RequestLS -> RequestLS.

Inductive Role : Set :=
 | Appraiser
 | Attester.
