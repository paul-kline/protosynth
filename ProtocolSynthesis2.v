
Inductive Noun : Set:=
  | VirusChecker
  | PCR.
  
Create HintDb eq_dec_db. 
Theorem eq_dec_noun : forall n1 n2 : Noun,
                    {n1 = n2} + {n1 <> n2}.
Proof. intros.   destruct n1, n2; 
  try (left;reflexivity); right; unfold not; intros H; inversion H.
Defined.  

Hint Resolve eq_dec_noun : eq_dec_db. 
Require Import String. 
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec. 
Inductive Adjective : Set :=
  | Name : Adjective
  | Hash : Adjective
  | Index : nat -> Adjective
  | Version : Adjective.

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
Hint Resolve eq_dec_adjective : eq_dec_db. 
Require Import Coq.Program.Equality. 
Inductive DescriptionR : Noun -> Adjective -> Set :=
  | pcrMR : forall n, DescriptionR PCR (Index n)
  | virusCheckerNameR : DescriptionR VirusChecker Name
  | virusCheckerVersionR : DescriptionR VirusChecker Version.
  
Theorem eq_dec_DescriptionR1 : 
forall n : Noun,
forall a : Adjective,
forall x y : DescriptionR n a,
x = y.
Proof. intros;
induction x; dependent induction y;
( reflexivity).
Qed.


Inductive Description : Set :=
  | descriptor (n : Noun) (a : Adjective) : DescriptionR n a -> Description.


Theorem eq_dec_Description : 
forall d1 d2 : Description,
{d1 = d2} + {d1 <> d2}. 
Proof. intros. destruct d1, d2.   
specialize eq_dec_adjective with a a0. intros. destruct H.
 specialize eq_dec_noun with n n0. intros.
destruct H. left. subst. specialize eq_dec_DescriptionR1 with n0 a0 d0 d.
intros. subst. reflexivity.
right. unfold not. intros. inversion H. contradiction.
right. unfold not. intros. inversion H. contradiction.
Qed.
Hint Resolve eq_dec_Description : eq_dec_db.
Hint Resolve eq_dec_DescriptionR1 : eq_dec_db.  
Definition HashT := nat. 
Definition VersionT := nat.
Add LoadPath "/users/paulkline/Documents/coqs/dependent-crypto".
Add LoadPath "/users/paulkline/Documents/coqs/cpdt/src".
Add LoadPath "C:\Users\Paul\Documents\coqs\dependent-crypto".
Add LoadPath "C:\Users\Paul\Documents\coqs\cpdt\src". 
Require Import MyShortHand.

Inductive type :=
| Nat : type
| Bool : type.

Theorem eq_dec_type : forall x y : type ,
{x = y} + { x <> y}.
Proof.
decide equality.
Qed.
Hint Resolve eq_dec_type : eq_dec_db.


Definition realType (t : type) : Set :=
match t with
 | Nat => nat
 | Bool => bool

end.

Inductive Sendable : Set :=
| Sendable_Measurement {t : type} : (realType t) -> Sendable
| RequestS : Description -> Sendable.

Theorem eq_dec_bool : forall b c : bool, 
{b = c} + {b <> c}.
Proof. decide equality. Qed.  


Require Import Coq.Program.Equality.
Require Import Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Peano_dec. 
Theorem sendable_measurment_inversion : forall t : type, forall n n1 : realType t, Sendable_Measurement n = Sendable_Measurement n1 -> n = n1.
Proof. intros.
inversion H; apply inj_pair2_eq_dec; apply eq_dec_type + apply H1.
Qed.
Theorem eq_dec_Sendable : forall x y : Sendable,
  { x = y} + {x <> y}.
Proof. intros. destruct x, y. destruct t, t0.
Case "Sendable_Measurement";
  SCase "realType Nat, realType Nat"; 
    specialize eq_nat_dec with r r0; intro nateq; destruct nateq.
    SSCase "Nats are eq";
       subst; left; reflexivity.
    SSCase "Nats NOT eq";
       subst; right; unfold not; intros hypo; 
       apply sendable_measurment_inversion in hypo; contradiction.    
Case "realType Nat, realType Bool";
  right; unfold not; intros stupid; inversion stupid.
Case "realType Bool, realType Nat";
  right; unfold not; intros stupid; inversion stupid.
Case "realType Bool, realType Bool";
  specialize eq_dec_bool with r r0; intro pp; destruct pp.
  SCase "bools are eq";
    left; subst; reflexivity.
  SCase "bools NOT eq";
    right; unfold not; intros hypo;
    apply sendable_measurment_inversion in hypo; contradiction.
Case "realType t, Description";
  right; unfold not; intros; inversion H.
Case "Description, realType t";
  right; unfold not; intros; inversion H.
Case "Description, Description";
  specialize eq_dec_Description with d d0; intro dd; destruct dd.
  SCase "descriptors are equal";
    left; subst; reflexivity.
  SCase "descriptors NOT equal";
    right; unfold not; intro pp; inversion pp; contradiction.
Qed.

Definition measurementType( d : Description) : type :=
match d with
 | descriptor n a r => match r with
    | pcrMR n => Nat
    | virusCheckerNameR => Nat
    | virusCheckerVersionR => Bool
end

end. 


Definition sendableType (s : Sendable) : Set :=
match s with
 | @Sendable_Measurement t _ =>  realType t
 | RequestS x => Description
end. 


Inductive Requirement (d : Description) :=
| requirement : ( realType (measurementType d) -> bool) -> Requirement d.


Check requirement.
Definition  des1 := (descriptor PCR (Index 1) (pcrMR 1)). 
Eval compute in (realType (measurementType des1)).
 (* 
 Check (requirement (fun (x : nat) => x > 7)).  *)
Definition req1 : (Requirement des1 ).
Search bool. 
apply requirement. simpl. exact ((fun (x : nat) => Nat.leb x 7)).
 
Defined.
Definition req2 := 
 requirement (des1) ((fun (x : nat) => Nat.leb x 7)).
 
Inductive Rule (mything : Description) :=  
| rule  {your : Description} : (Requirement your) -> Rule mything
| free : Rule mything
| never : Rule mything
| multiReqAnd : Rule mything ->Rule mything -> Rule mything
| multiReqOr : Rule mything -> Rule mything -> Rule mything.   


Inductive PrivacyPolicy :=
| EmptyPolicy : PrivacyPolicy
| ConsPolicy {d :Description}: 
    Rule d -> 
    PrivacyPolicy -> PrivacyPolicy. 
Check req1.

Definition myRule1 := rule (des1) (requirement (descriptor PCR (Index 2) (pcrMR 2))
 (fun x : nat => Nat.leb x 9)).
Check myRule1.
Check ConsPolicy.
Print myRule1. 
Definition myPrivacyPolicy := ConsPolicy myRule1 EmptyPolicy.
 
 


Definition myrequirement1 := fun (x : nat) => (x > 7).

Inductive Session :=
 | Send : Sendable -> Session -> Session
 | Receive : Sendable -> Session -> Session
 | Branch : bool -> Session -> Session -> Session
 | Stop : Session
 . 
Inductive GlobalSession :=
 | SendtoRight : Sendable -> GlobalSession -> GlobalSession
 | SendtoLeft : Sendable -> GlobalSession -> GlobalSession
 | GlobalStop : GlobalSession.
 
Inductive Side :=
 | LeftSide : Side
 | RightSide : Side.
Theorem eq_dec_side : forall s1 s2 : Side,
{s1 = s2} + {s1<> s2}. Proof.
decide equality.
Qed.
   
Fixpoint globalToSide (g : GlobalSession) (s : Side) : Session :=
 match g with
 | SendtoRight t g' => match s with
    | LeftSide => Send t (globalToSide g' s)
    | RightSide => Receive t (globalToSide g' s)
    end
 | SendtoLeft t g' => match s with
    | LeftSide => Receive t (globalToSide g' s)
    | RightSide => Send t (globalToSide g' s)
    end
 | GlobalStop => Stop
end.

Definition seven : realType Nat := 7.
  
Definition global1 := SendtoRight (Sendable_Measurement seven) (SendtoRight (@Sendable_Measurement Bool false)
 (SendtoLeft (@Sendable_Measurement Nat 3) GlobalStop)).
Eval compute in globalToSide global1 LeftSide.
Eval compute in globalToSide global1 RightSide.

Fixpoint getRule (p : PrivacyPolicy) (someoneWants : Description): Rule someoneWants .
refine match p with
 | EmptyPolicy => never someoneWants
 | @ConsPolicy myd r pol => if eq_dec_Description someoneWants myd then 
         _

    else 
    getRule pol someoneWants
end. 
subst. exact r. Defined.   

Definition networkSend (s : Sendable) : unit.
exact tt. Defined.  
Definition networkReceive (n : nat) : Sendable.
Admitted. 

Fixpoint GlobalToLocal (g : GlobalSession) (s : Side) (pol : PrivacyPolicy) : Session :=
match (s,g) with
 | (LeftSide, SendtoLeft sendable gsess)  => Receive sendable (GlobalToLocal gsess s pol) 
 | (RightSide, SendtoRight sendable gsess)  => Receive sendable (GlobalToLocal gsess s pol)
 | (LeftSide, SendtoRight sendable gsess) => 
   match sendable with
     | @Sendable_Measurement _ _ => Send sendable (GlobalToLocal gsess s pol)
     | RequestS d => Send sendable
        match networkReceive 1 with 
         |  @Sendable_Measurement t val => match getR
         |  RequestS d => Stop
        end
   end

 | (RightSide, SendtoLeft sendable session)  => Stop

 | (_, GlobalStop) => Stop
end.


Definition  privacy { n1 n2 : Noun} {a1 a2 : Adjective} 
(x : (DescriptionR n1 a1)):= (DescriptionR n2 a2, 
(fun ( x : (realType (DescriptionR n1 a1))) => Prop ) ). 

Check privacy.  





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
 

Require Import Coq.Arith.Peano_dec. 
Require Import Coq.Classes.EquivDec.


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





