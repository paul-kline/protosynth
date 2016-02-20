
Inductive Noun : Set:=
  | VirusChecker
  | PCR.
  
Print Noun.

Require Import String. 
 
Inductive Adjective : Set :=
  | Name : Adjective
  | Hash : Adjective
  | Index : nat -> Adjective
  | Version : Adjective. 
(* 
Inductive type : Set :=
  | Nat
  | Bool.
 *)

Inductive DescriptionR : Noun -> Adjective -> Set :=
  | pcrM : forall n, DescriptionR PCR (Index n) 
  | virusCheckerName : DescriptionR VirusChecker Name
  | virusCheckerVersion : DescriptionR VirusChecker Version.
    
Require Import Coq.Relations.Relation_Definitions.

Check pcrM.
Check DescriptionR.
Check DescriptionR PCR. (* 
Check DescriptionR PCR Index. *)
Check pcrM.

Definition HashT := nat. 
Definition VersionT := nat.
Add LoadPath "/users/paulkline/Documents/coqs/dependent-crypto".
Add LoadPath "/users/paulkline/Documents/coqs/cpdt/src".
Add LoadPath "C:\Users\Paul\Documents\coqs\dependent-crypto".
Add LoadPath "C:\Users\Paul\Documents\coqs\cpdt\src". 
(*Require Import Crypto.*)

Inductive type :=
| Nat : type
| Bool : type.

Inductive Sendable : Set :=
| Sendable_Measurement : type -> Sendable
| RequestS {n: Noun} {a: Adjective} : DescriptionR n a -> Sendable.

Definition measurementType {n} {a}( m : DescriptionR n a) : type :=
match m with
 | pcrM n => Nat
 | virusCheckerName => Nat
 | virusCheckerVersion => Nat
end%type.

Fixpoint realType (t : type) : Set :=
match t with
 | Nat => nat
 | Bool => bool

end.

Inductive Requirement {n : Noun} {a : Adjective} (d : DescriptionR n a) :=
| requirement : ( realType (measurementType d) -> Prop) -> Requirement d. 
Check requirement.
Eval compute in (realType (measurementType (pcrM 1))).
 (* 
 Check (requirement (fun (x : nat) => x > 7)).  *)
Definition req1 : (Requirement (pcrM 1)).
apply requirement. simpl. exact ((fun (x : nat) => x > 7)).
Defined.
 
Definition req2 := 
 requirement (pcrM 1) ((fun (x : nat) => x > 7)).
 
Inductive Privacy { n : Noun} {a : Adjective} (my : DescriptionR n a) :=  
| privreq { n2 : Noun} {a2 : Adjective} {your : DescriptionR n2 a2} : (Requirement your) -> Privacy my
| free : Privacy my
| multiReq : Privacy my -> Privacy my -> Privacy my.   

Check req1.

Definition myPrivacy := privreq (pcrM 1) (requirement (pcrM 2) (fun x : nat => x > 9)).
Check myPrivacy.
 
     
 := requirement (fun (x : nat) => x > 7). 
 
Definition privacy { n n2:Noun} {a a2: Adjective} (x : (DescriptionR n a)) := 
  ( DescriptionR n2 a2, 
       (realType (measurementType d)) => Prop)  ).
Check privacy.

Definition myrequirement1 := fun (x : nat) => (x > 7).

Definition myprivacy1 :=     

Definition  privacy { n1 n2 : Noun} {a1 a2 : Adjective} 
(x : (DescriptionR n1 a1)):= (DescriptionR n2 a2, 
(fun ( x : (realType (DescriptionR n1 a1))) => Prop ) ). 

Check privacy.  


Require Import Coq.Classes.EquivDec. 


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

Theorem eq_dec_Sendable : forall x y : Sendable,
  { x = y} + {x <> y}.
Proof. intros; destruct x, y;
 try rec_eq;
 try (left; reflexivity);
 try ( right; unfold not; intros; inversion H).
Defined.         
  

Check measurementType.
Eval compute in (measurementType (pcrM 4)). 
 
Open Scope string_scope. (* 
Definition measure {noun} {a} (m : DescriptionR noun a) : measurementType m :=
match m with
 | pcrM n => n * n
 | virusCheckerName => "Hello!!!"
 | virusCheckerVersion => 7
end.  *)

Inductive request : Set :=
 | nothin : request
 | somethin {no} {a} : DescriptionR no a -> request -> request.
 
Definition myrequest := somethin (pcrM 2) (somethin virusCheckerName nothin).


(* Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.
Instance EqDec_DescriptionR {n0} {a} `(@EqDec (DescriptionR n0 a) eq eq_equivalence) : EqDec_eq (DescriptionR n0 a).
 *)
 
 Require Import Coq.Logic.Decidable. 
Theorem eq_dec_noun : forall n1 n2 : Noun,
                    {n1 = n2} + {n1 <> n2}.
Proof. intros.   destruct n1, n2; 
  try (left;reflexivity); right; unfold not; intros H; inversion H.
Defined.  

Require Import Coq.Arith.Peano_dec. 
Require Import Coq.Classes.EquivDec.

(* Currently with rec_eq, we can prove decidablilty of
adjectives that (at one level deep only) take arguments of 
nat, bool, and unit. *)
Theorem eq_dec_adjective : forall a1 a2 : Adjective,
                    {a1 = a2} + {a1 <> a2}.
Proof. intros; destruct a1, a2;
  try rec_eq;
  try (left;reflexivity);
  try (right; unfold not; intros H; inversion H).
Defined. 

(* 
Definition eq_dec_DescriptionR {n1 n2} {a1 a2} (m1 : (DescriptionR n1 a1)) 
                                            (m2 : (DescriptionR n2 a2)) : .
Proof. case_eq n1.  (n1 = n2). destruct n1. , n2, a1, a2.                       
                              { m1 = m2} + {m1 <> m2}. 
     *)
Fixpoint member {n1} {a1} (m : DescriptionR n1 a1) (rs : request) : bool :=
match rs with
 | nothin => false
 | @somethin n2 a2  x xs => if eq_dec_noun n1 n2 then 
                              if eq_dec_adjective a1 a2 then true 
                              else false
                            else false
end.

Fixpoint request_eq (r1 r2 : request) : bool :=
 match r1 with
 | nothin => match r2 with
    | nothin => true
    | somethin _ _ => false
    end

 | somethin  x x0 => andb (member x r2) (request_eq x0 r2)
end.

Add LoadPath "/users/paulkline/Documents/coqs/dependent-crypto".
Add LoadPath "/users/paulkline/Documents/coqs/cpdt/src".
Add LoadPath "/users/paulkline/Documents/coqs/mysfProgress". 
(* Require Import Signing.  *)

Inductive SessionT : Type :=
 | StopT : SessionT
 | SendT : Sendable  -> SessionT -> SessionT
 | ReceiveT : Sendable -> SessionT -> SessionT. 
 
Inductive GlobalSession : Type :=
 | globalSession : SessionT -> SessionT -> GlobalSession.

Add LoadPath "/users/paulkline/Documents/coqs".
Require Import MyShortHand.

Fixpoint isValidGlobal ( g : GlobalSession) : Prop.
destruct g. destruct s eqn : sessLEFT. destruct s0 eqn : sessRIGHT.
Case "Stop, Stop"; exact True.
Case "Stop, Send _";  exact False.
Case "Stop, Receive _"; exact False.
destruct s0 eqn : sessRIGHT.
Case "Send _, Stop"; exact False.
Case "Send _, Send _"; exact False.
Case "Send _, Receive _".   generalize eq_dec_Sendable.  intros X. specialize X with s1 s3. destruct X. 
    SCase "types param of messages are equal"; exact True; (*  generalize message_eq_dec; intros.
      clear sessRIGHT. rewrite <- e in m0.   specialize X with t m m0; destruct X.
      SSCase "messages are equal"; exact True.
      SSCase "message NOT equal"; exact False. *)
    SCase "types param of message NOT equal". exact False.
 destruct s0  eqn : sessRIGHT.
Case "Receive _, Stop"; exact False.
Case "Receive _, Send _"; generalize eq_dec_Sendable.  intros X. specialize X with s1 s3; destruct X. 
    SCase "types param of messages are equal"; exact True. (*  generalize message_eq_dec; intros.
      clear sessRIGHT. rewrite <- e in m0.   specialize X with t m m0; destruct X.
      SSCase "messages are equal"; exact True.
      SSCase "message NOT equal"; exact False. *)
    SCase "types param of message NOT equal"; exact False.
Case "Receive _, Receive _"; exact False.
Defined.

Inductive ValidatedGlobalSessionType : Type :=
  | validGlobalSession : { g | isValidGlobal g} -> ValidatedGlobalSessionType.

Fixpoint sessionAppend (s1 s2 : SessionT) : SessionT :=
match s1 with
 | StopT => s2
 | SendT x x0 => SendT x (sessionAppend x0 s2)
 | ReceiveT x x0 => ReceiveT x (sessionAppend x0 s2)
end. 
Notation "s1 '++' s2" := (sessionAppend s1 s2).
 
Fixpoint globalAppend (g1 g2 : GlobalSession) : GlobalSession :=
match g1,g2 with
 | globalSession l r, globalSession l2 r2 => globalSession (l ++ l2) (r ++ r2) 
end.
Notation "g1 '++' g2" := (globalAppend g1 g2). 


Fixpoint createReturns (req : request) : GlobalSession :=
 match req with
 | nothin => globalSession StopT StopT
 | somethin t ls => (globalSession (ReceiveT (measurementType t) StopT) 
               (SendT (measurementType t) StopT)) 
               ++
               (createReturns ls)
end.


Fixpoint synth'  (rq : request) (sendBackReqs : request) : GlobalSession  :=
 match rq with
 | nothin => createReturns sendBackReqs
 | somethin r ls => (globalSession (SendT (measurementType r) StopT) 
                                  (ReceiveT (measurementType r) StopT))
                     ++
                     (synth' ls (somethin r sendBackReqs))
end. 

Definition synth (rq : request) : GlobalSession := synth' rq nothin.

(*Inductive DescriptionR : Noun -> Adjective -> Set :=
  | pcrM : forall n, DescriptionR PCR (Index n) 
  | virusCheckerName : DescriptionR VirusChecker Name
  | virusCheckerVersion : DescriptionR VirusChecker Version.
    *)
Definition pcrRequestPart := pcrM 1.
Definition vcNameRequestPart := virusCheckerName.
Definition vcVersionRequestPart := virusCheckerVersion .
Definition pcrRequestPart2 := pcrM 2.
Definition myRequest := somethin pcrRequestPart 
                        (somethin vcNameRequestPart
                        (somethin vcVersionRequestPart
                        (somethin pcrRequestPart2 nothin)
                        )).
Eval compute in synth nothin.
Eval compute in synth myRequest.





