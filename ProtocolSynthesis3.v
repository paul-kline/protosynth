
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
  | descriptor {n : Noun} {a : Adjective} : DescriptionR n a -> Description.


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

Add LoadPath "/users/paulkline/Documents/coqs/dependent-crypto".
Add LoadPath "/users/paulkline/Documents/coqs/cpdt/src".
Add LoadPath "C:\Users\Paul\Documents\coqs\dependent-crypto".
Add LoadPath "C:\Users\Paul\Documents\coqs\cpdt\src". 
Require Import MyShortHand.

Inductive type : Set :=
| Nat : type
| Bool : type.

Theorem eq_dec_type : forall x y : type ,
{x = y} + { x <> y}.
Proof.
decide equality.
Qed.
Hint Resolve eq_dec_type : eq_dec_db.


Definition typeDenote (t : type) : Set :=
match t with
 | Nat => nat
 | Bool => bool

end.

Definition measurementType( d : Description) : type :=
match d with
 | descriptor r => match r with
    | pcrMR n => Nat
    | virusCheckerNameR => Nat
    | virusCheckerVersionR => Bool
end

end.
Definition measurementDenote (d: Description) :=
match d with
 | descriptor r => match r with
    | pcrMR n => nat
    | virusCheckerNameR => nat
    | virusCheckerVersionR => bool
end

end.


Inductive Message : Set :=
| Sendable_Measurement (d: Description) : (measurementDenote d) -> Message
| RequestS : Description -> Message
| StopMessage : Message.
Theorem eq_dec_bool : forall b c : bool, 
{b = c} + {b <> c}.
decide equality.
Qed. 


Require Import Coq.Program.Equality.
Require Import Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Peano_dec.
 
Theorem sendable_measurment_inversion : 
forall d : Description, forall n n1 : (measurementDenote d), 
@Sendable_Measurement d n = @Sendable_Measurement d n1 -> n = n1.
Proof. intros.
inversion H. apply inj_pair2_eq_dec. apply eq_dec_Description. Print existT.   apply H1.

Qed.
Theorem eq_dec_Message : forall x y : Message,
  { x = y} + {x <> y}.
Proof. intros. destruct x, y. specialize eq_dec_Description with d d0; intros.


destruct H. subst. specialize sendable_measurment_inversion with d0 m0 m.
intros.  
destruct d0. 
destruct n,a.
destruct d.
    simpl in m0, m;
specialize eq_nat_dec with m m0; intros;
destruct H0 as [eq |neq]; subst; ( (left; reflexivity) +
right; unfold not; intros; apply neq; apply symmetry in H0;
apply H in H0; rewrite H0; reflexivity).
Admitted.

Definition sendableType (s : Message) : Set :=
match s with
 | @Sendable_Measurement d _ =>  measurementDenote d
 | RequestS x => Description
 | StopMessage => unit
end. 


Inductive Requirement (d : Description) :=
| requirement : ( (measurementDenote d) -> bool) -> Requirement d.


Check requirement.
Definition  des1 := (descriptor (pcrMR 1)). 
Eval compute in (measurementDenote des1).
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

Definition myRule1 := rule (des1) (requirement (descriptor (pcrMR 2))
 (fun x : nat => Nat.leb x 9)).
Check myRule1.
Check ConsPolicy.
Print myRule1. 
Definition myPrivacyPolicy := ConsPolicy myRule1 EmptyPolicy.
 
 


Definition myrequirement1 := fun (x : nat) => (x > 7).

Inductive Session :=
 | Send : Message -> Session -> Session
 | Receive : (Message -> Session) -> Session
 | Branch : bool -> Session -> Session -> Session
 | Stop : Session
 . 
Inductive GlobalSession :=
 | SendtoRight : Message -> GlobalSession -> GlobalSession
 | SendtoLeft : Message -> GlobalSession -> GlobalSession
 | GlobalStop : GlobalSession.
 
Inductive Side :=
 | LeftSide : Side
 | RightSide : Side.
Theorem eq_dec_side : forall s1 s2 : Side,
{s1 = s2} + {s1<> s2}. Proof.
decide equality.
Qed.
   

Definition seven := 7.
  Print Sendable_Measurement. Print Description. 
Definition global1 := SendtoRight (Sendable_Measurement (descriptor (pcrMR 2)) 7) 
 (SendtoRight (Sendable_Measurement (descriptor (pcrMR 3)) 3)
 (SendtoLeft (Sendable_Measurement (descriptor (pcrMR 4)) 5) GlobalStop)).
 
(* Takes a privacy policy and gives you back a rule, no matter what.
If the requested item has no explicit rule. The default is to never give it away.*)
Fixpoint getRule (p : PrivacyPolicy) (someoneWants : Description): Rule someoneWants .
refine match p with
 | EmptyPolicy => never someoneWants
 | @ConsPolicy myd r pol => if eq_dec_Description someoneWants myd then 
         _

    else 
    getRule pol someoneWants
end. 
subst. exact r. Defined.   

Definition networkSend (m : Message) : unit.
exact tt. Defined.  
Definition networkReceive (n : nat) : Message.
Admitted. 



Inductive Action : Set :=
 | ASend : Action
 | AReceive : Action.
 Theorem eq_dec_Action : forall x y : Action,
 {x = y} + {x <>y }.
 Proof. decide equality. Qed.
 
 Require Import Coq.Lists.List. 
 Definition measure (d: Description) : measurementDenote d.
 Admitted.
Inductive  Continuence : Set :=
 | more : Description -> Continuence
 | final : bool -> Continuence.
 
Inductive RequestItem : Set :=
 | requestItem (d : Description) : (Requirement d) -> RequestItem.
 Theorem eq_dec_RequestItem : forall x y : RequestItem,
 {x = y} + {x <> y}. Proof. intros.
 Admitted.   
Inductive RequestLS : Set :=
 | emptyRequestLS : RequestLS
 | ConsRequestLS : RequestItem -> RequestLS -> RequestLS.
Fixpoint reduceUnresolved (d : Description) (v : measurementDenote d)
(ls : RequestLS) : option RequestLS. refine match ls with
 | emptyRequestLS => Some emptyRequestLS
 | ConsRequestLS r x0 => match r with
      | requestItem dr reqment => if eq_dec_Description dr d then
          match reqment with
            | requirement _ f => match f _ with
               | true => Some x0
               | false => None (* give up *)
              end
          end
        else
          match reduceUnresolved d v x0 with 
            | Some some => Some (ConsRequestLS r some)
            | None => None
          end
     end
 end. rewrite <- e in v. exact v. Defined. 
Inductive Role : Set :=
 | Appraiser
 | Attester. 
Theorem eq_dec_Role: forall x y : Role, {x = y} + {x <> y}. 
Proof. decide equality. Qed. 
(*handleRequest
input: privacyPolicy, measurmentRequest
output: measument | request | no (aka Stop)
*) 
Inductive HandleRequestResponse :=
 | hr_Mess : PrivacyPolicy -> Message -> RequestItem -> HandleRequestResponse. 

Definition freeRequirement (d : Description): Requirement d:= 
 requirement d (fun _ => true).
Definition neverRequirement (d : Description): Requirement d:= 
 requirement d (fun _ => false).
Check neverRequirement. 
Fixpoint handleRequest (pp : PrivacyPolicy) (d : Description) : 
(PrivacyPolicy * Message * RequestItem):=
 match pp with
 | EmptyPolicy => (EmptyPolicy, StopMessage, requestItem d (neverRequirement d))  (*by default, do not give away*)
 | @ConsPolicy dp rule_d pp' => if (eq_dec_Description dp d) 
    then
      match rule_d with
       | @rule _ your reqrment => (pp, RequestS your, requestItem your reqrment)
       | free _ => (pp, Sendable_Measurement d (measure d), requestItem d (freeRequirement d) )
       | never _ => (pp, StopMessage, requestItem d (neverRequirement d)) (*don't matter *)
       | multiReqAnd _ rule1 morerules => (pp, StopMessage, requestItem d (neverRequirement d)) (* TODO *)
       | multiReqOr _ rule1 morerules => (pp, StopMessage, requestItem d (neverRequirement d)) (* TODO *)
      end
    else
     match handleRequest pp' d with
       | (ppres,messres,reqRes) => (@ConsPolicy dp rule_d ppres,messres,reqRes)
     end
 end. 
 
Fixpoint getProtocol (n : nat) (role : Role) (omes :  list Message) (myPriv : PrivacyPolicy) 
 (toRequest : RequestLS) (unresolved : RequestLS): Session :=
match n with
| O => Stop
| S n' =>
match omes with
 | nil => match toRequest with
     | emptyRequestLS => match role with
         | Appraiser => Stop (* nothin left *)
         | Attester => Receive (fun m => match m with
             | Sendable_Measurement d v => match reduceUnresolved d v unresolved with
                 | Some newUnresolvedState => getProtocol n' Attester nil myPriv emptyRequestLS newUnresolvedState
                 | None => Send StopMessage Stop (*fails to meet my reqs I give up *)
                 end 
             | RequestS d => match handleRequest myPriv d with 
                | (newpp,mess,reqItem) => Send mess 
                     (getProtocol n' Attester nil newpp emptyRequestLS (ConsRequestLS reqItem unresolved) )
                end
             | StopMessage => Stop
             end)
         end
     | ConsRequestLS reqItem reqls' => match reqItem with
         | requestItem d reqment => Send (RequestS d) 
            (getProtocol n' role nil myPriv reqls' 
               (ConsRequestLS (requestItem d reqment) unresolved) ) 
         end
     end
 | cons mes mesls => Send mes (getProtocol n' role mesls myPriv toRequest unresolved)
 end

end. 

 
 
 
 
   

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





