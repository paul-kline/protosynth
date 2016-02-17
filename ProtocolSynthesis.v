(* 

Class Measurable (A : Set) : Set := {
  description : A ;
  value       : A 
  }. *)
(*   
Print Measurable.
 *)
(* Inductive pcr : Set :=
 | pcrdescription : nat -> pcr
 | pcrvalue       : nat -> pcr.
  *)(* 
Instance PCR : Measurable pcr.
apply Build_Measurable. Abort. *)

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

Inductive type : Set :=
  | Nat
  | Bool.
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
Require Import Crypto.
  
Definition measurementType {n} {a}( m : DescriptionR n a) : Sendable :=
match m with
 | pcrM n => Nat
 | virusCheckerName => Nat
 | virusCheckerVersion => Nat
end%type.

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
Require Import Signing. 

Inductive SessionT : Type :=
 | StopT : SessionT
 | SendT : SendableT  -> SessionT -> SessionT
 | ReceiveT : SendableT -> SessionT -> SessionT. 
 
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
Case "Send _, Receive _".   generalize eq_type_dec.  intros X; specialize X with t t0. destruct X. 
    SCase "types param of messages are equal"; exact True; (*  generalize message_eq_dec; intros.
      clear sessRIGHT. rewrite <- e in m0.   specialize X with t m m0; destruct X.
      SSCase "messages are equal"; exact True.
      SSCase "message NOT equal"; exact False. *)
    SCase "types param of message NOT equal". exact False.
 destruct s0  eqn : sessRIGHT.
Case "Receive _, Stop"; exact False.
Case "Receive _, Send _"; generalize eq_type_dec.  intros X; specialize X with t t0; destruct X. 
    SCase "types param of messages are equal"; exact True. (*  generalize message_eq_dec; intros.
      clear sessRIGHT. rewrite <- e in m0.   specialize X with t m m0; destruct X.
      SSCase "messages are equal"; exact True.
      SSCase "message NOT equal"; exact False. *)
    SCase "types param of message NOT equal"; exact False.
Case "Receive _, Receive _"; exact False.
Defined.

Inductive ValidatedGlobalSessionType : Type :=
  | validGlobalSession : { g | isValidGlobal g} -> ValidatedGlobalSessionType.

Fixpoint sessionAppend (s1 s2 : Session) : Session :=
match s1 with
 | Stop => s2
 | Send x x0 => Send x (sessionAppend x0 s2)
 | Receive x x0 => Receive x (sessionAppend x0 s2)
end. 
Notation "s1 '++' s2" := (sessionAppend s1 s2).
 
Fixpoint globalAppend (g1 g2 : GlobalSession) : GlobalSession :=
match g1,g2 with
 | globalSession l r, globalSession l2 r2 => globalSession (l ++ l2) (l2 ++ r2) 
end.
Notation "g1 '++' g2" := (globalAppend g1 g2). 

Fixpoint createReturns (req : list Set) : GlobalSession :=
 match req with 
  | nil => Global Stop Stop
  | t :: ls => Global (Receive Basic Stop) (Send (basic  
Fixpoint synth'  (rq : request) (sendBackReqs : list Set) : GlobalSession  :=
 match rq with
 | nothin => createReturns sendBackReqs
 | somethin no a x x0 => _
end

Definition synth (rq : request) : GlobalSession := synth' rq [].




