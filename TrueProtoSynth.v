(* Goals:
1. Generate protocols from:
     a. A list of what one would like to know about the other
     b. One's own privacy policy

2. The protocol generator should:
     a. Ask for all items listed in (1)a.
     b. Never violate the privacy policy in (1)b. (*constraint *)
     c. Never generate protocols that don't "match up."
        i.e. all protocols are valid and will execute properly.
     d. Always terminate.
*)

(* The first step is to define what it is for which we would like to ask. Hence "nouns". *)

Inductive Noun : Set:=
  | VirusChecker
  | PCR.
  
Create HintDb eq_dec_db. 
Theorem eq_dec_noun : forall n1 n2 : Noun, {n1 = n2} + {n1 <> n2}.
Proof. intros.   destruct n1, n2; 
  try (left;reflexivity); right; unfold not; intros H; inversion H.
Defined.

Hint Resolve eq_dec_noun (*: eq_dec_db.*).
 
(*Require Import String.*) 
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.

 (* Now we define what it is we would like to know about these nouns. *)
Inductive Attribute : Set :=
  | Name : Attribute
  | Hash : Attribute
  | Index : nat -> Attribute
  | Version : Attribute.

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



Theorem eq_dec_attribute : forall a1 a2 : Attribute,
                    {a1 = a2} + {a1 <> a2}.
Proof. decide equality; rec_eq.
Defined. 
Hint Resolve eq_dec_attribute : eq_dec_db. 
Require Import Coq.Program.Equality.

(*We only want to disallow nonsensical combinations, like a (PCR, version),
 hence this relation. *)
Inductive DescriptionR : Noun -> Attribute -> Set :=
  | pcrMR : forall n, DescriptionR PCR (Index n)
  | virusCheckerNameR : DescriptionR VirusChecker Name
  | virusCheckerVersionR : DescriptionR VirusChecker Version.
  
Theorem eq_dec_DescriptionR1 : 
forall n : Noun,
forall a : Attribute,
forall x y : DescriptionR n a,
x = y.
Proof. intros;
induction x; dependent induction y;
( reflexivity).
Defined.
Hint Resolve eq_dec_DescriptionR1. 

(* This 'extra step' is done simply so that comparison between descriptors
is 'easy.'It is much more involved to be able to compare indexed types. *)

Inductive Description : Set :=
  | descriptor {n : Noun} {a : Attribute} : DescriptionR n a -> Description.


Theorem eq_dec_Description : 
forall d1 d2 : Description,
{d1 = d2} + {d1 <> d2}. 
Proof. intros. destruct d1, d2.   
specialize eq_dec_attribute with a a0. intros. destruct H.
 specialize eq_dec_noun with n n0. intros.
destruct H. left. subst. specialize eq_dec_DescriptionR1 with n0 a0 d0 d.
intros. subst. reflexivity.
right. unfold not. intros. inversion H. contradiction.
right. unfold not. intros. inversion H. contradiction.
Defined. 
Hint Resolve eq_dec_Description . (*: eq_dec_db.
Hint Resolve eq_dec_DescriptionR1 : eq_dec_db.  *)

Add LoadPath "/users/paulkline/Documents/coqs/dependent-crypto".
Add LoadPath "/users/paulkline/Documents/coqs/cpdt/src".
Add LoadPath "C:\Users\Paul\Documents\coqs\dependent-crypto".
Add LoadPath "C:\Users\Paul\Documents\coqs\cpdt\src". 
Require Import MyShortHand.

(*This defines what the type of measuring these things should be. *)

Definition measurementDenote (d: Description) :=
match d with
 | descriptor r => match r with
    | pcrMR n => nat
    | virusCheckerNameR => nat
    | virusCheckerVersionR => bool
end

end.


(*Let us add to our building blocks by defining what a message can be.
  In it's simplest form, a message can only be a request (RequestS) or a response to a request.
  It turns out a response to a request can take the form of any of the 3 defined messages. 
   1. You can comply with the request and send a "Sendable_Measurement."
   2. You can conditionally comply with the request by countering with another request, depending on its
      result. 
   3. You can refuse all together with a StopMessage.
  A StopMessage is also used to indicate good termination, i.e. I'm done.
  
  
  We must "lock in" what it is that we have measured. We do this in
  the type of Sendable_Measurement.*)

Inductive Message : Set :=
| Sendable_Measurement (d: Description) : (measurementDenote d) -> Message
| RequestS : Description -> Message
| StopMessage : Message.
Theorem eq_dec_bool : forall b c : bool, 
{b = c} + {b <> c}.
decide equality.
Defined.
Hint Resolve  eq_dec_bool.  


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
Hint Resolve  sendable_measurment_inversion. 



Theorem lemma1 : forall d : Description, forall m1 m2 : (measurementDenote d), {m1 = m2} + {m1 <> m2}.
Proof. intros. destruct d. destruct d; simpl in m1; simpl in m2; (apply nat_eq_eqdec) || (apply bool_eqdec).
Qed.
Hint Resolve  lemma1. 
(*
Theorem eq_dec_Message : forall x y : Message,
  { x = y} + {x <> y}. Proof. intros. *)
  
  Ltac not_eq := let x := fresh "beats" in (let y := fresh "beats" in  ((try right); unfold not; intros x; inversion x as [y];
     (try (apply inj_pair2_eq_dec in y); auto with eq_dec_db)  )).
Theorem eq_dec_Message : forall x y : Message,
  { x = y} + {x <> y}.   
Proof. intros. destruct x. destruct y.   destruct (eq_dec_Description d d0). subst. destruct (lemma1 d0 m m0); subst.
left. refl. right. not_eq. not_eq. not_eq. not_eq.
destruct y. not_eq.
destruct (eq_dec_Description d d0). subst. left. refl.
not_eq. not_eq. destruct y. not_eq. not_eq. left; refl.
Defined.
Hint Resolve  eq_dec_Message.  


(* Here we begin specificiation of requirements. So not only do I want a particular measurment,
   but I want it to be certain values. *) 

Inductive Requirement (d : Description) :=
| requirement : ( (measurementDenote d) -> bool) -> Requirement d.

Check requirement.

(*Examples *)
Definition  des1 := (descriptor (pcrMR 1)). 
Eval compute in (measurementDenote des1).
Definition req1 : (Requirement des1 ).
Search bool. 
apply requirement. simpl. exact ((fun (x : nat) => Nat.leb x 7)).
Defined.
Definition req2 := 
 requirement (des1) ((fun (x : nat) => Nat.leb x 7)).
 
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
Check req1.

Definition myRule1 := rule (des1) (requirement (descriptor (pcrMR 2))
 (fun x : nat => Nat.leb x 9)).
Check myRule1.
Check ConsPolicy.
Print myRule1. 
Definition myPrivacyPolicy := ConsPolicy myRule1 EmptyPolicy.
 
 


Definition myrequirement1 := fun (x : nat) => (x > 7).

(* Here is what a session is: We either send something
   and then another Session, or receive a message and 
   produce another session. A Branch is shown here, but never used.*)
Inductive Session :=
 | Send : Message -> Session -> Session
 | Receive : (Message -> Session) -> Session
 | Stop : Session
 .

(* This helps with protocol generation. *)
Inductive Action : Set :=
 | ASend : Action
 | AReceive : Action.

 Theorem eq_dec_Action : forall x y : Action,
 {x = y} + {x <>y }.
 Proof. decide equality. Defined.
 Hint Resolve  eq_dec_Action. 
 
 Require Import Coq.Lists.List.
 
 (* placeholder measurement function. need this to exist *) 
 Definition measure (d: Description) : measurementDenote d.
 Proof. destruct d. destruct d. simpl. exact n.
 simpl. exact 0.
 simpl. exact true. 
 Defined.
 
 (*A RequestItem is used to compose a list of the items and requirements upon those items in an attestation *)
Inductive RequestItem : Set :=
 | requestItem (d : Description) : (Requirement d) -> RequestItem.
 Theorem eq_dec_RequestItem : forall x y : RequestItem,
 {x = y} + {x <> y}. Proof. intros. destruct x. destruct y. destruct (eq_dec_Description d d0). subst.
 destruct r0. (*Need function equality. Do I need equality on this? *)      
 Admitted.   
Inductive RequestLS : Set :=
 | emptyRequestLS : RequestLS
 | ConsRequestLS : RequestItem -> RequestLS -> RequestLS.
 
 (* Now we get into functions needed to define the getProtocol function. 
    Due to coqs linear nature, we must define in this order, but know that
    it's existence was only deamed necessary during the construction of getProtocol. 
    
    In short, the purpose of this function is to reduce the size of the list of the 
    things we are waiting on measurements for. The option type is used to indicate
    if the requirement posed upon the value v has failed to be met.
    *)
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
Proof. decide equality. Defined.
Hint Resolve eq_dec_Role. 

Definition freeRequirement (d : Description): Requirement d:= 
 requirement d (fun _ => true).
Definition neverRequirement (d : Description): Requirement d:= 
 requirement d (fun _ => false).
Check neverRequirement.
 
 
 (* note that the rule is removed from the privacy policy. This is to prevent measurement deadlock
 situations. Everything not expressly in the privacy policy is rejected. Therefore, you can't ask
 for the same thing twice. *)
 (*What to do when you receive a request? This controversial issue is handled here.
    We give back a triplet. The privacy policy returned has the requested item removed from the policy 
    (if there is no rule for a request, the request is denied) . This prevents being asked twice for the 
    same thing. We probably don't want this. I will think about an alternative.
    The message is the response that will be sent. We either send the measured value, send a counter request, or deny
    the request with a response of StopMessage. The last item may seem odd, always returning a RequestItem as well.
    This is because of the one case when we counter the request with another request. Most likely we will want to 
    make sure the measured value we request meets certain expectations. Therefore we need to also return the requirement
    imposed by these expectations. In the other cases (sending stop or sending the measurement) we "make up" a return value.
    This can probably be handled better than this. 
 *)
Fixpoint handleRequest (pp : PrivacyPolicy) (d : Description) : 
(PrivacyPolicy * Message * RequestItem):=
 match pp with
 | EmptyPolicy => (EmptyPolicy, StopMessage, requestItem d (neverRequirement d))  (*by default, do not give away*)
 | @ConsPolicy dp rule_d pp' => if (eq_dec_Description dp d) 
    then
      match rule_d with
       | @rule _ your reqrment => (pp', RequestS your, requestItem your reqrment)
       | free _ => (pp', Sendable_Measurement d (measure d), requestItem d (freeRequirement d) )
       | never _ => (pp', StopMessage, requestItem d (neverRequirement d)) (*don't matter *)
       | multiReqAnd _ rule1 morerules => (pp', StopMessage, requestItem d (neverRequirement d)) (* TODO *)
       | multiReqOr _ rule1 morerules => (pp', StopMessage, requestItem d (neverRequirement d)) (* TODO *)
      end
    else
     match handleRequest pp' d with
       | (ppres,messres,reqRes) => (@ConsPolicy dp rule_d ppres,messres,reqRes)
     end
 end. 
 
Definition canSend (ls : list Description) (priv : PrivacyPolicy) : option Description :=
(match ls with
 | nil => None
 | cons d ds => 
   (match (handleRequest priv d) with 
     | (_, Sendable_Measurement d _,_) => Some d  
     | _ => None
     end)
end).
   
(* the above is only a definition (as opposed to fixpoint). this helps us make sure we respond "in order" *)


(* Now that we know some measurement value, can we ease any requirements stated in the privacy policy? 
Stay tuned to find out! *)

Fixpoint reducePrivacy (d : Description) (v : (measurementDenote d)) (priv : PrivacyPolicy) : PrivacyPolicy.
refine (
match priv with
 | EmptyPolicy => EmptyPolicy
 | @ConsPolicy dp rule_d pp' =>
      match rule_d with
       | @rule _ your reqrment => if (eq_dec_Description d your) then
          (match reqrment with
            | requirement _ f => if (f _) then ConsPolicy (free dp) (reducePrivacy d v pp')
                               else ConsPolicy (never dp) (reducePrivacy d v pp')
          end)
          else (ConsPolicy (rule your reqrment) (reducePrivacy d v pp'))
       | _ => @ConsPolicy dp rule_d (reducePrivacy d v pp')
      end
    
 end). subst. exact v. Defined.
 
 (* main course *)
 
 
 Inductive VarID :=
  | receivedMESSAGE : VarID
  | toSendMESSAGE : VarID
  | variden : nat -> VarID
  . 
  Theorem eq_dec_VarID : forall x y : VarID, {x = y} + {x <> y}.
  Proof. intros. destruct x,y; try (left; reflexivity).
  right; unfold not;intros;inversion H.
  right; unfold not;intros;inversion H.
  right; unfold not;intros;inversion H.
  right; unfold not;intros;inversion H.
  right; unfold not;intros;inversion H.
  right; unfold not;intros;inversion H.
  decide equality. rec_eq. Defined.
  
  Inductive Const :=
   | constAction : Action -> Const
   | constValue (d: Description) : (measurementDenote d) -> Const 
   | constRequest : Description -> Const
   | constStop : Const.
   
Inductive Term :=
 | variable : VarID -> Term
 | const : Const -> Term
 .
Inductive Condition :=
 | CanSend :  Condition
 | IsSend :  Condition
 | IsMeasurement : Term -> Condition
 | IsRequest : Term -> Condition
 | IsStop : Term -> Condition
.


Inductive Statement :=
 | SendStatement : Term -> Statement
 | ReceiveStatement : Term -> Statement
 | ReduceStatewithMeasurement : Term -> Statement
 | HandleRequest : Term -> Statement
 | Assignment : Term -> Term -> Statement
 | Choose : Condition -> Statement -> Statement -> Statement
 | Chain : Statement -> Statement -> Statement
 | StopStatement : Statement
 | Skip : Statement
.

Notation "'IFS' x 'THEN' y 'ELSE' z" := (Choose x y z)(at level 80, right associativity). 
Notation "x '>>' y" := (Chain x y)  (at level 60, right associativity).
(*Notation "(x >> .. >> y)" := (Chain x .. (Chain y StopMessage) ..).*)

Inductive VarState :=
 | varState : list (VarID*Const) -> VarState. 
Inductive ProState :=
 | proState : Action -> PrivacyPolicy -> RequestLS -> RequestLS -> list Description
      -> ProState.
Inductive State :=
 state : VarState -> ProState -> State.       

Fixpoint varSubst'' (t : Term) (ls : (list (VarID*Const))) : option Const :=
match t with
 | variable vid => match ls with
                     | nil => None
                     | cons pr ls' => if (eq_dec_VarID (fst pr) vid) then 
                           Some (snd pr)
                          else 
                           varSubst'' t ls'
                   end
 | const x => Some ( x)
end. 
Definition varSubst' (t: Term) (vst : VarState) : option Const :=
 match vst with
    | varState ls => varSubst'' t ls
 end. 
Definition varSubst (t : Term) (st : State ) : option Const :=
match st with
 | state varst _ => varSubst' t varst
end.

Inductive Participant :=
 |  ATTESTER
 |  APPRAISER. 
 Theorem eq_dec_Participant : forall x y : Participant, {x = y} + {x <> y}.
 Proof. decide equality. Defined.
    
Inductive NetworkMessage :=
 networkMessage : Participant -> Participant -> Const -> NetworkMessage. 
Definition Network := list NetworkMessage.

(* When we send a message, it gets appended to the end of the list. This makes receiving
in the correct order easier. *)
Fixpoint sendOnNetwork (from : Participant) (to : Participant) (m : Const) (n : Network) : Network :=
 match n with
 | nil => cons (networkMessage from to m) nil
 | cons n1 nls => cons n1 (sendOnNetwork from to m nls) 
end. 

Fixpoint receiveOnNetwork (from : Participant) (me : Participant) (n : Network) : option Const :=
 match n with
 | nil => None
 | cons msg n' => match msg with
                   | networkMessage nfrom nto x1 => match 
                      ((eq_dec_Participant nfrom from),(eq_dec_Participant nto me)) with 
                      | (left _, left _) => Some x1
                      | (_,_) => receiveOnNetwork from me n'
                      end
                  end
end.
  
Definition net_isEmpty ( n : Network) : bool :=
 match n with
 | nil => true
 | cons x x0 => false
end.

Definition reduceStateWithMeasurement (v : Const) (st : State) : option State := 
 match v with
 | constAction _ => Some st
 | constRequest _ => Some st
 | constStop => Some st
 | constValue d denotedVal => (match st with
                                | state varst  prost=> (match prost with
                                    | proState a pp toReq myUnresolved tosend => 
                                       (match (reduceUnresolved d denotedVal myUnresolved) with
                                         | Some newUnresolvedState => Some ( 
                                            state varst 
                                              (proState a (reducePrivacy d denotedVal pp) toReq     
                                                        newUnresolvedState tosend))
                                         | None => None
                                       end)
                                    end)
                              end)
 end.  

Fixpoint handleRequest' (pp : PrivacyPolicy) (d : Description) : 
(PrivacyPolicy * Const * RequestItem):=
 match pp with
 | EmptyPolicy => (EmptyPolicy, StopMessage, requestItem d (neverRequirement d))  (*by default, do not give away*)
 | @ConsPolicy dp rule_d pp' => if (eq_dec_Description dp d) 
    then
      match rule_d with
       | @rule _ your reqrment => (pp', CReRequestS your, requestItem your reqrment)
       | free _ => (pp', Sendable_Measurement d (measure d), requestItem d (freeRequirement d) )
       | never _ => (pp', StopMessage, requestItem d (neverRequirement d)) (*don't matter *)
       | multiReqAnd _ rule1 morerules => (pp', StopMessage, requestItem d (neverRequirement d)) (* TODO *)
       | multiReqOr _ rule1 morerules => (pp', StopMessage, requestItem d (neverRequirement d)) (* TODO *)
      end
    else
     match handleRequest pp' d with
       | (ppres,messres,reqRes) => (@ConsPolicy dp rule_d ppres,messres,reqRes)
     end
 end. 
 
Definition canSend (ls : list Description) (priv : PrivacyPolicy) : option Description :=
(match ls with
 | nil => None
 | cons d ds => 
   (match (handleRequest priv d) with 
     | (_, Sendable_Measurement d _,_) => Some d  
     | _ => None
     end)
end).


Fixpoint evalUntilReceive (me : Participant) (to: Participant) (statement : Statement) (st : State) (n : Network) : 
  (Statement * State * Network) :=
match statement with
 | SendStatement x => match (varSubst x) with 
                       | None => (VariableSubstError, st, n)
                       | Some c => (Skip, st, (sendOnNetwork from to))
 | ReceiveStatement x => (ReceiveStatement x,st,n)
 | ReduceStatewithMeasurement x => match (varSubst x) with 
                                    | None => (VariableSubstError, st, n)                                    
                                    | Some v => (match (reduceStateWithMeasurement v st) with 
                                                  | None => (MeasurementRequirementNotMet,st, n)
                                                  | Some newst => 
                                                     (Skip, newst, n)
                                                 end)
 | HandleRequest x => _
 | Assignment x x0 => _
 | Choose x x0 x1 => _
 | Chain x x0 => _
 | StopStatement => _
end




Fixpoint DualEval (leftSide rightSide : Statement) (leftState rightState : State) (n : Network) :=
 match leftSide with
 | SendStatement t => match (varSubst t leftState) with 
                         | None => (VariableSubstError 
 | ReceiveStatement x => _
 | ReduceStatewithMeasurement x => _
 | HandleRequest x => _
 | Assignment x x0 => _
 | Choose x x0 x1 => _
 | Chain x x0 => _
 | StopStatement => _
end
 

  
Definition OneProtocolStep : Statement :=
  (* first step is to find out if we're sending or receiving. *)
  IFS IsSend
   THEN
    IFS CanSend
      THEN 
        ((Assignment (variable toSendMESSAGE) getMsgToSnd) >>
         SendStatement (variable toSendMESSAGE) >>
         StopStatement
        )
      ELSE 
         SendStatement (const (constMessage StopMessage)) >>
         StopStatement
   ELSE 
    ReceiveStatement (variable (receivedMESSAGE)) >>
    IFS (IsMeasurement (variable (receivedMESSAGE)))
      THEN 
       ReduceStatewithMeasurement (variable (receivedMESSAGE))
      ELSE
       (IFS (IsRequest (variable (receivedMESSAGE)))
         THEN 
           HandleRequest (variable (receivedMESSAGE))
         ELSE (*we must have received a stop *)
           StopStatement
        
       ).  

Check OneProtocolStep.
Print OneProtocolStep.

   
Inductive IsDual : Statement ->  Statement -> Prop:=
 | sendtoleft {s} {r} : IsDual (SendStatement s) (ReceiveStatement r)
 | sendVsChain {x} {y} {z} : forall m, IsNotSend m -> IsNotChain m -> IsDual (SendStatement x) (
 | flipIsDual {x} {y} : IsDual x y -> IsDual y x 
 | chaindual {l1} {l2}: (Chain l1 l2)
 | sendtoleft  (ReceiveStatement r) (SendStatement s) : IsDual (SendStatement s) (ReceiveStatement r) .
 | ReceiveStatement x => _
 | ReduceStatewithMeasurement x => _
 | HandleRequest x => _
 | Assignment x x0 => _
 | Choose x x0 x1 => _
 | Chain x x0 => _
 | StopStatement => _
end
  
Fixpoint getProtocol (n : nat) (a: Action) (myPriv : PrivacyPolicy) 
 (toRequest : RequestLS) (unresolved : RequestLS) (toSend : list Description): Session :=
(match n with
| O => match a with 
    | ASend => (Send StopMessage) Stop
    | AReceive => Receive (fun m => Send StopMessage Stop) 
    end
| S n' =>
(match a with
 | ASend => 
   (match (canSend toSend myPriv) with
     | Some d => 
      (* if there was something queued up, I should expect to receive something since we are excluding 'and' *)
      Send (Sendable_Measurement d (measure d)) (getProtocol n' AReceive myPriv toRequest unresolved (tail toSend))
     | None => 
     (*I've been told I have to send something. I either am not allowed to send the thing, or 
     there was nothing to send. No matter what, the other guy is expecting a send, so send we must. *)
      (match toRequest with
     | emptyRequestLS => Send StopMessage Stop (* If I can't send a measurment and I have nothing to request,
       I guess we're done. *)
     | ConsRequestLS reqItem reqls' => (match reqItem with
         | requestItem d reqment => Send (RequestS d) (*Something to request! I sent, so now I expect to receive with reduced torequest state, but built up unresolved state*) 
            (getProtocol n' AReceive myPriv reqls' 
               (ConsRequestLS (requestItem d reqment) unresolved) toSend )
         end)
     end)
    end)
 
 
 
(* I've been instructed to receive. As per our agreement, always send right after a receive.
Unless, of course, it was a StopMessage, then stop. *)
 | AReceive => Receive (fun m => match m with
             | Sendable_Measurement d v => (match reduceUnresolved d v unresolved with
                 | Some newUnresolvedState => 
                    getProtocol n' ASend (reducePrivacy d v myPriv) toRequest newUnresolvedState toSend
                 | None => Send StopMessage Stop (*fails to meet my reqs I give up *)
                 end) 
             | RequestS d => (match handleRequest myPriv d with 
                 | (_, StopMessage,_) => Send StopMessage Stop
                 | (newpp,mess,reqItem) => Send mess 
                     (getProtocol n' AReceive newpp emptyRequestLS (ConsRequestLS reqItem unresolved) toSend)
                 end)
             | StopMessage => Stop
             end)
 end)
 end). 
Ltac findForExists hypo := match goal with
| [ hypo :context[?T]   |- exists T, _ ] => exists T; (try reflexivity)
  end.
 
Require Import Omega. 
Theorem WillReceive : forall n a pp rls un ls m s, m <> StopMessage ->  (getProtocol (S n) a pp rls un ls) = Send m s -> 
 exists f, s = Receive f. 
Proof. intro n. induction n. intros. simpl in H0. destruct a. destruct (canSend ls pp).
findForExists H0. inversion H0.  reflexivity. destruct rls.
inversion H0. subst. elim H. reflexivity. destruct r.
findForExists H0. inversion H0. reflexivity. inversion H0.
intros. simpl in H0. destruct a. destruct (canSend ls pp). inversion H0. eauto.
 destruct rls. inversion H0. subst. elim H. reflexivity. destruct r. inversion H0. 
findForExists H3. inversion H0. Qed. 

Add LoadPath "C:\Users\Paul\Documents\coqs\protosynth\cpdt\src".
Add LoadPath "/nfs/users/paulkline/Documents/coqs/protosynth/cpdt/src".
Add LoadPath "C:\Users\Paul\Documents\coqStuff\protosynth\cpdt\src".
Require Import CpdtTactics. 
Theorem WillSend : forall n a pp rls un ls f, (getProtocol (S n) a pp rls un ls) = Receive f -> 
( forall m, m <> StopMessage -> exists m2 s', (f m) = Send m2 s').
Proof. intro n. induction n. intros. simpl in H. destruct a. destruct (canSend ls pp). inversion H.
destruct rls. inversion H. destruct r. inversion H. inversion H. destruct m eqn : M. destruct (reduceUnresolved d m0 un). eauto. eauto.
destruct (handleRequest pp d). destruct p. destruct m0. exists (Sendable_Measurement d0 m0). eauto. eauto. eauto.
elim H0. reflexivity. intros. simpl in H. destruct a. destruct (canSend ls pp). inversion H. subst. destruct rls. inversion H.
destruct r. inversion H. simpl_eq. simpl in H. destruct m. inversion H. subst.
destruct (reduceUnresolved d m un). destruct (canSend ls (reducePrivacy d m pp)).
eauto. destruct rls. eauto. destruct r0. eauto. eauto. inversion H. destruct (handleRequest pp d). destruct p.
destruct m. eauto. eauto. eauto. elim H0. reflexivity.
Qed.
Hint Resolve  WillSend. 

Check (Receive _). 
Inductive IsValid : Session -> Session -> Prop :=
 | both_stop : IsValid Stop Stop
 | lr_stop : IsValid (Send StopMessage Stop) Stop
 | rl_stop : IsValid Stop (Send StopMessage Stop)
 | lr_send {x} {y} {m} {f}: IsValid x y -> (f m = y) -> IsValid (Send m x) (Receive f) 
 | rl_send {x} {y} {m} {f}: IsValid x y -> (f m = x) -> IsValid (Receive f) (Send m y). 
 
Hint Constructors IsValid. 
Example example1 : IsValid 
(Send StopMessage Stop) 
(Receive (fun p => match p with
   | Sendable_Measurement d x => Send StopMessage Stop
   | RequestS x => Send StopMessage Stop
   | StopMessage => Stop
end)).
Proof. simpl. intros. eauto. Qed. (*  apply lr_stop. reflexivity. Qed. *)     
 
Example example2 : IsValid 
(Receive (fun p => match p with
   | Sendable_Measurement d x => Send StopMessage Stop
   | RequestS x => Send StopMessage Stop
   | StopMessage => Stop
end))
(Send StopMessage Stop).
Proof. simpl. intros. eauto. Qed. (*   apply rl_stop. reflexivity. Qed. *)


Example example3 : IsValid 
(Send (RequestS (descriptor (pcrMR 1))) 
 (Receive (fun p => match p with
   | Sendable_Measurement d x => Send StopMessage Stop
   | RequestS x => Send StopMessage Stop
   | StopMessage => Stop
end)))

(Receive (fun p => (Send StopMessage Stop))).
Proof. intros. cbn.  simpl. Print lr_send. 
apply @lr_send with (Send StopMessage Stop).
apply @rl_send with (Stop). auto.
auto.
auto.         Qed.  (*  specialize example1. intros. specialize example2; intros.
apply @lr_send with (Send StopMessage Stop) . assumption.  reflexivity. Qed.
*)
Example example4 : IsValid 
(Receive (fun p => (Send StopMessage Stop)))

(Send (RequestS (descriptor (pcrMR 1))) 
 (Receive (fun p => match p with
   | Sendable_Measurement d x => Send StopMessage Stop
   | RequestS x => Send StopMessage Stop
   | StopMessage => Stop
end)))

.
Proof. apply @rl_send with (Send StopMessage Stop).
apply @lr_send with Stop.
auto. auto. auto. Qed. 

Definition lenientPolicy := ConsPolicy (free (descriptor (pcrMR 1))) 
(ConsPolicy (free (descriptor (pcrMR 2))) EmptyPolicy). 

Definition lenientishPolicy := ConsPolicy (rule (descriptor (pcrMR 1) ) (requirement (descriptor (pcrMR 1)) (fun x :nat => beq_nat x 1))) 
(ConsPolicy (rule (descriptor (pcrMR 2)) (requirement (descriptor (pcrMR 2)) (fun x :nat => beq_nat x 2)) ) EmptyPolicy).
Check getProtocol.
Definition thingIWant1 := requestItem (descriptor (pcrMR 1)) 
  (requirement (descriptor (pcrMR 1)) (fun x :nat => beq_nat x 1)) .
Definition thingIWant2 := requestItem (descriptor (pcrMR 2)) 
  (requirement (descriptor (pcrMR 2)) (fun x :nat => beq_nat x 2)) .
  (*types must match :D ) *)
Definition thingsIwant := ConsRequestLS thingIWant1 emptyRequestLS.

Definition attesterproto1 := getProtocol 5 AReceive lenientPolicy emptyRequestLS emptyRequestLS nil .
Definition appraiserProto1 := getProtocol 5 ASend EmptyPolicy thingsIwant emptyRequestLS nil.

Definition attesterproto2 := getProtocol 5 AReceive EmptyPolicy emptyRequestLS emptyRequestLS nil.
Definition appraiserProto2 := getProtocol 5 ASend EmptyPolicy thingsIwant emptyRequestLS nil.

Definition attesterproto3 := getProtocol 5 AReceive lenientishPolicy emptyRequestLS emptyRequestLS nil.
Definition appraiserProto3 := getProtocol 5 ASend lenientPolicy thingsIwant emptyRequestLS nil.


Eval compute in appraiserProto1.


Definition reduce (m : Message) (sess : Session) :=
match sess with
 | Send x x0 => sess
 | Receive f => Receive (fun _ => f m) 
 | Stop => Stop
end. 


Theorem subValid : forall m x f, IsValid (Send m x) (Receive f) -> IsValid x (f m).
Proof. intros. inversion H. subst. exact H3.
Qed.
Hint Resolve  subValid.
Theorem subValid2 : forall m x f, IsValid (Receive f) (Send m x) -> IsValid (f m) x.
Proof. intros. inversion H. subst.
subst. exact H3.
Qed. 
Hint Resolve subValid2.

Theorem reducingIsOkay : forall f m x, IsValid (Send m x) (Receive f) <-> 
  IsValid (Send m x) (reduce m (Receive f)).
Proof. split.  intros. simpl. apply subValid in H. apply @lr_send  with ( f m). exact H.
reflexivity.
intros. simpl. simpl in H. apply @lr_send with (f m). inversion H. subst. exact H3.
reflexivity.           
 Qed.
 Hint Resolve  reducingIsOkay. 

Theorem reducingIsOkay2 : forall f m x, IsValid (Receive f) (Send m x) <-> 
  IsValid (reduce m (Receive f)) (Send m x) .
Proof. split.  intros. simpl. apply subValid2 in H. apply @rl_send  with ( f m). exact H.
reflexivity.
intros. simpl. simpl in H. apply @rl_send with (f m). inversion H. subst. exact H3. 
reflexivity.
 Qed.
 Hint Resolve reducingIsOkay2. 

Definition getNext (m : Message) (sess : Session) : Session :=
match sess with
 | Send x x0 => x0
 | Receive x => x m 

 | Stop => Stop
end.

Definition smallStep (dos : (Session * Session)) : option (Session * Session):=
 match dos with 
  | ((Send m s1'), (Receive f)) => Some (s1', (f m)) 
  | ((Receive f), (Send m s2')) => Some ((f m), s2')
  | _ => None
 end.
 
 Eval cbn in getNext (Sendable_Measurement 
    (descriptor (pcrMR 1)) 1) (getNext _ appraiserProto1). 
Fixpoint smallStepn (n : nat) (x : (Session*Session)): ((Session*Session) *nat) :=
  match n with
  | O => (x,0)
  | S n' => match (smallStep x) with 
              | Some r => smallStepn n'  r
              | None   => (x,n)
            end
  end.

(*
Definition x := Eval cbn in  smallStep (smallStep (smallStep (appraiserProto1, attesterproto1))).
Print x .
*)
Fixpoint bigStep (s1 : Session) (s2 : Session) : option (Session*Session) :=
 match (s1,s2) with 
  | ((Send m s1'), (Receive f)) => bigStep s1' (f m) 
  | ((Receive f), (Send m s2')) => bigStep (f m) s2'
  | (Stop, Stop) => Some (Stop, Stop)
  | _ => None
 end.
 
Eval cbn in (bigStep appraiserProto1 attesterproto1).
Eval compute in appraiserProto1.
 
 Import Coq.Program.Equality. 
Example eijeifjfij : (bigStep appraiserProto1 attesterproto1) = Some (Stop,Stop).
Proof. unfold appraiserProto1. unfold attesterproto1. cbn. unblock_goal. simpl. cbn.
cbn. eauto. simpl_eq. reflexivity.
Qed.
Hint Resolve  eijeifjfij. 
(*
Eval compute in smallStep (smallStep (smallStep (appraiserProto2, attesterproto2))).  *)
Example eefffees2 : (bigStep appraiserProto2 attesterproto2) = Some (Stop,Stop).
Proof.  unfold appraiserProto2. unfold attesterproto2. simpl.
reflexivity. Qed.
Hint Resolve  eefffees2.  


Theorem IsValid_IsValid : forall x y, IsValid x y -> IsValid y x.
Proof. intros. induction H; auto || eauto.
Qed.
Hint Resolve IsValid_IsValid.  

Theorem bigStep_implies_IsValid : forall x y : Session, (bigStep x y) = Some (Stop,Stop) -> 
 IsValid x y. Proof. intro. induction x. simpl. destruct y eqn:what. simpl.
 intros.
 inversion H.
 intros. apply IHx in H. eauto.
 intros. inversion H.
 intros. inversion H0.
 intros. eauto.
    destruct y. eauto.
    inversion H0.
    inversion H0. intros. 
    simpl in H. inversion H.
    intros. simpl in H. inversion H.
    intros. simpl in H.
    destruct y; (try inversion H).
    auto.
    Qed.
    Hint Resolve bigStep_implies_IsValid. 
Example example5 : IsValid appraiserProto1 attesterproto1.
Proof. intros. apply bigStep_implies_IsValid.
  cbn. unblock_goal. simpl_eq. reflexivity.
  Qed.
  
  Check getProtocol.
  
Ltac proto' := match goal with
 |  [ H : IsValid (Send ?M ?X) (Receive ?F) |- _ ] => 
           apply @lr_send with (F M)
           end. (* 
  | IsValid (Receive ?F) (Send ?M ?X) => 
           apply @rl_send with (F M)
  | IsValid Stop Stop  => 
           apply  both_stop
  | IsValid Stop  (Send StopMessage Stop) => 
           apply lr_stop
  | IsValid (Send StopMessage Stop) Stop => 
           apply rl_stop
  end.*)
Ltac proto := match goal with 
  | [  |- IsValid (Send ?M ?X) (Receive ?F)] => 
           apply @lr_send with (F M)
  | [  |- IsValid (Receive ?F) (Send ?M ?X)] => 
           apply @rl_send with (F M)
  | [  |- IsValid Stop Stop ] => 
           apply  both_stop
  | [  |- IsValid Stop  (Send StopMessage Stop)] => 
           apply lr_stop
  | [  |- IsValid (Send StopMessage Stop) Stop] => 
           apply rl_stop
  end.
Ltac pH H:= simpl in H; match H with 
  | context[ IsValid (Send ?M ?X) (Receive ?F)] => 
           apply @lr_send with (F M) in H; idtac "here"
  | context[IsValid (Receive ?F) (Send ?M ?X)] => 
           apply @rl_send with (F M) in H
  | context[IsValid Stop Stop] => 
           apply  both_stop in H 
  | context[IsValid Stop  (Send StopMessage Stop)] => 
           apply lr_stop in H 
  | context[IsValid (Send StopMessage Stop) Stop] => 
           apply rl_stop in H
           end. 


  Eval compute in bigStep appraiserProto3 attesterproto3. 
Example efijefijeg3 : IsValid appraiserProto3 attesterproto3.
unfold appraiserProto3. unfold attesterproto3. simpl. proto. 
unblock_goal. simpl_eq.  
proto. simpl_eq. proto. simpl_eq. proto. auto. auto.
simpl_eq. refl. simpl_eq. auto. simpl_eq. reflexivity.
Qed.

Ltac proto_simpler' iden := match iden with
 | IsValid ?X ?Y => progress (simpl_eq || proto' iden || auto)
  | ?X = ?Y => auto
  end.
Ltac proto_simpler := match goal with
  | [ |- IsValid ?X ?Y] => progress (simpl_eq || proto || auto)
  | [ |- ?X = ?Y] => auto
  end.
  Example testa : IsValid appraiserProto3 attesterproto3.
  Proof. unfold appraiserProto3. unfold attesterproto3. repeat proto_simpler.
  Qed.

  
  
Theorem WillStop_Receive : forall n a pp rls un f ls, (getProtocol (S n) a pp rls un ls) = Receive f ->
  f StopMessage = Stop. 
Proof. intros.  destruct a. simpl in H. destruct (canSend ls pp).  inversion H.
destruct rls. inversion H. destruct r. inversion H. simpl in H. inversion H.
auto. Qed.
Hint Resolve  WillStop_Receive. 
Theorem willReceive : forall n pp rls un ls, exists f, (getProtocol (S n) AReceive pp rls un ls) = Receive f. 
Proof. intros. destruct n. simpl. eauto. simpl. eauto.
Qed.

Theorem IsValid_WillStoprl : 
 forall n pp rls un ls, IsValid (getProtocol (S n) AReceive pp rls un ls) (Send StopMessage Stop).
 intros. (proto_simpler).  proto_simpler. proto_simpler. auto. Qed.
 Hint Resolve IsValid_WillStoprl.
 
Theorem IsValid_WillStoplr : 
 forall n pp rls un ls, IsValid (Send StopMessage Stop) (getProtocol (S n) AReceive pp rls un ls).
  intros. proto_simpler. proto_simpler. auto. auto. Qed.
  Hint Resolve IsValid_WillStoplr.

Theorem WillStop_Send : forall n a pp rls un r ls, (getProtocol n a pp rls un ls) = Send StopMessage r ->
  r = Stop. 
Proof. intros. destruct n. simpl in H. inversion H.
simpl in H. destruct a. destruct (canSend ls pp). inversion H.
destruct rls. inversion H. reflexivity.    
destruct r0. inversion H. inversion H. refl. inversion H. refl.
inversion H. simpl in H. destruct a. destruct (canSend ls pp). inversion H. destruct rls. inversion H. refl.
destruct r. destruct r0. inversion H. destruct r0. inversion H. destruct r0. inversion H.
 inversion H. Qed.

Hint Resolve WillStop_Send. 
Theorem wellduh_eq_dec_Attribute :
 forall x, exists p : x =x, eq_dec_attribute  x x= left p.
 intros. case_eq (eq_dec_attribute x x). intros. exists e. reflexivity.
 intros. assert (x = x). refl. contradiction. Qed.
 Hint Resolve wellduh_eq_dec_Attribute. 
 
 Theorem wellduh_eq_dec_Noun :
forall x, exists p : x =x, eq_dec_noun  x x= left p.
 intros. case_eq (eq_dec_noun x x). intros. exists e. reflexivity.
 intros. assert (x = x). refl. contradiction. Qed.
 Hint Resolve wellduh_eq_dec_Noun. 
 
Theorem wellduh_eq_dec_Description : 
forall x, exists p : x = x, eq_dec_Description x x = left p.
 intros. case_eq (eq_dec_Description x x). intros. exists e. reflexivity.
 intros. assert (x = x). refl. contradiction. Qed.
 Hint Resolve  wellduh_eq_dec_Description. 
 
 
Theorem IguessThatsOkay :
IsValid Stop ((Receive (fun _ => Stop))).
Admitted.

Ltac elim_let := match goal with 
  | [  |- IsValid _ (let _ := ?T in _) ] => destruct T
  | [  |- IsValid  (let _ := ?T in _) _ ] => destruct T
  | [  |- context[let _ := ?T in _] ] => destruct T
  | [  |- let _ := ?T in _ ] => destruct T
  
  end.
  (*
  Add LoadPath "C:\Users\Paul\Documents\coq\cpdt".
Require Import CpdtTactics.  *)

Ltac protosimpler := repeat (simpl; proto_simpler). 
Theorem IsValid_1_1 : forall  pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  IsValid (getProtocol (1) ASend pp1 rls1 un1 ls1) (getProtocol (1) AReceive pp2 rls2 un2 ls2).
  Proof. intros. simpl. destruct rls1. destruct (canSend ls1 pp1). proto_simpler.
  destruct (reduceUnresolved d (measure d) un2).  auto. auto.
  destruct (reduceUnresolved d (measure d) un2). eauto. eauto.  eauto.
  proto_simpler. proto_simpler.  auto. auto.
  destruct (canSend ls1 pp1). proto_simpler.
  destruct (reduceUnresolved d (measure d) un2). eauto. eauto. 
  destruct (reduceUnresolved d (measure d) un2). auto. auto.        
  destruct r. proto_simpler. destruct (handleRequest pp2 d). destruct p. destruct m.
  proto_simpler.   eauto. auto. protosimpler.  protosimpler.
  destruct (handleRequest pp2 d). destruct p. destruct m. auto. auto.
  auto. Qed.
  
  Hint Resolve  IsValid_1_1. 

Theorem IsValid_0_0 : forall  pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  IsValid (getProtocol (0) ASend pp1 rls1 un1 ls1) (getProtocol (0) AReceive pp2 rls2 un2 ls2).
  intros. proto_simpler. proto_simpler. auto. auto.
  Qed.
  Hint Resolve  IsValid_0_0.  
   (*
  Theorem IsValidPrivacy : forall  pp1 pp2 pp1' rls1 rls2 un1 un2 ls1 ls2 n,
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n) AReceive pp2 rls2 un2 ls2) ->
  IsValid (getProtocol (S n) ASend pp1' rls1 un1 ls1) (getProtocol (S n) AReceive pp2 rls2 un2 ls2).
  Proof. intros. induction pp1.  proto_simpler.  destruct (canSend ls1 pp1'). proto_simpler. destruct (getProtocol n AReceive pp1' rls1 un1 (tl ls1)).
  destruct (reduceUnresolved d (measure d) un2). simpl.     
  *)
  Axiom succValid : forall  n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2 ,
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n) AReceive pp2 rls2 un2 ls2)
  ->
  IsValid (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol (n) AReceive pp2 rls2 un2 ls2).
   
   Theorem sendStopAll : forall n  pp1 rls1 un1 ls1, IsValid (Send StopMessage Stop)
  (getProtocol (n) AReceive pp1 rls1 un1 ls1).
  intro. induction n. intros. simpl. proto_simpler. auto. auto. intros. simpl. proto_simpler. auto. auto.
  Qed.
  Hint Resolve sendStopAll. 
  
  Ltac sendstop := match goal with
    | [ |- IsValid (getProtocol _ AReceive _ _ _ _) (Send StopMessage Stop)] =>
       apply IsValid_IsValid; apply sendStopAll
    | [ |- IsValid (Send StopMessage Stop) (getProtocol _ AReceive _ _ _ _) ] =>
        apply sendStopAll
       end. 
             
             (*
  Theorem nDontMatta : forall  n pp1 rls1 un1 ls1 proto2,
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1)  proto2 -> 
  IsValid (getProtocol (n) ASend pp1 rls1 un1 ls1) proto2.
  Proof. intro. induction n. intros. proto_simpler. simpl in H. destruct (canSend ls1 pp1). inversion H. subst. proto_simpler.    
  proto_simpler. proto_simpler. proto_simpler.
  apply IsValid_IsValid. apply IguessThatsOkay.   subst.   apply sendStopAll.   simpl in H. simpl.   inversion H. subst. simpl. 
  destruct (canSend ls1 pp1). proto_simpler.        inversion H. subst. proto_simpler. destruct   inversion H. subst.   simpl.     
  
  Theorem IsValidSucc : forall  n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2 ,
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n) AReceive pp2 rls2 un2 ls2) -> 
  IsValid (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol (n) AReceive pp2 rls2 un2 ls2).
  Proof. intros. (* inversion H.  einduction H.  eqn: d.  n. intros. apply IsValid_zero.
  intros. proto_simpler.  
  destruct (canSend ls1 pp1). proto_simpler.   
  destruct (reduceUnresolved d (measure d) un2).
  destruct (canSend ls2 (reducePrivacy d (measure d) pp2)). 
  proto_simpler. 
  destruct (reduceUnresolved d0 (measure d0) un1). eapply IHn.  proto_simpler.       ap.
  Proof. intro. induc  *)
  Theorem IsValidAnyParams : forall  pp1 n pp2 rls1 rls2 un1 un2 ls1 ls2 ,
  IsValid (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol ( n) AReceive pp2 rls2 un2 ls2) ->
  forall pp1', 
  IsValid (getProtocol (n) ASend pp1' rls1 un1 ls1) (getProtocol (n) AReceive pp2 rls2 un2 ls2).
  Proof. intro. induction pp1. intros. destruct pp1'. apply H.
      destruct n. intros. apply IsValid_zero.
  intros. proto_simpler.      intros. apply H.    induction n. intros. apply IsValid_zero.
  intros. 
  apply IHn.     destruc 
  Theorem IsValidInc : forall  n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2 ,
  IsValid (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol ( n) AReceive pp2 rls2 un2 ls2) -> 
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n) AReceive pp2 rls2 un2 ls2).
  Proof. intro. destruct n. intros. apply IsValid_inc1. intros. 
  proto_simpler.  
  destruct (canSend ls1 pp1). proto_simpler.   
  destruct (reduceUnresolved d (measure d) un2).
  destruct (canSend ls2 (reducePrivacy d (measure d) pp2)). 
  proto_simpler. 
  destruct (reduceUnresolved d0 (measure d0) un1). eapply IHn.  proto_simpler.       ap.
  Proof. intro. induction n. ap
  Theorem IsValidevverything : forall  n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2 ,
  IsValid (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol ( n) AReceive pp2 rls2 un2 ls2).
  Proof. intro. induction n. apply IsValid_zero. intros. simpl.
  destruct (canSend ls1 pp1). progress proto_simpler.
  destruct (reduceUnresolved d (measure d) un2). apply IsValid_IsValid. apply IHn.
  apply IsValid_IsValid. apply sendStopAll.
  destruct (reduceUnresolved d (measure d) un2). auto. auto.
  destruct rls1. proto_simpler. auto. auto. destruct r. proto_simpler.
  destruct (handleRequest pp2 d). destruct p. destruct m. crush. apply IHn.        apply sendStopAll.    
  destruct ( canSend ls2 (reducePrivacy d (measure d) pp2)).
  proto_simpler.  
  destruct (reduceUnresolved d0 (measure d0) un1).
  apply succValid. apply I
  
  *)

  
  Check getProtocol. 
  Inductive Parms :=
    | parmsc : nat -> Action -> PrivacyPolicy ->  
                              RequestLS -> RequestLS -> list Description
                              -> Parms
    | justStop : Parms.
  Definition getprotocol (parms : Parms) :=
    match parms with
     | parmsc n act pp rls unls ls => 
        getProtocol n act pp rls unls ls
     | justStop => Stop
    end. 
 Definition flipAction (p : Parms) : Parms :=
  match p with
 | parmsc x a x1 x2 x3 x4 => 
    parmsc x
 (match a with
 | ASend => AReceive
 | AReceive => ASend
end) 
x1 x2 x3 x4
 | d => d
end.

Definition getAction (p : Parms) : Action :=
 match p with
 | parmsc x a x1 x2 x3 x4 => a
 | _ => ASend
end.
(*
  Definition whatsthatmessage (pars : Parms) (_ : getAction pars = ASend) :
   (Message * Parms). intros. destruct (getprotocol pars) eqn:P. destruct pars. destruct n.
  simpl in H. unfold getprotocol in P. rewrite H in P.  simpl in P . inversion P. subst.
    
  exact (StopMessage, justStop).
  
  simpl in H.
  simpl in P. rewrite H in P. simpl in P. 
  destruct (canSend l p).
  exact (Sendable_Measurement d (measure d), parmsc n AReceive p r r0 (tl l)).
  destruct r.
   exact (StopMessage,justStop). (* parmsc n a p emptyRequestLS r0 l). *)
   destruct r.
   exact (RequestS d, parmsc n AReceive p r1 (ConsRequestLS (requestItem d r) r0) l).
   inversion P. 
   destruct pars. simpl in H. subst.
   unfold getprotocol in P.
   
   destruct n. simpl in P. inversion P.
   simpl in P. destruct (canSend l p). inversion P.
   destruct r. inversion P. destruct r. inversion P.
   inversion P. 
   destruct pars. simpl in H. subst . destruct n. simpl in P. inversion P. simpl in P. destruct (canSend l p). inversion P. destruct r. inversion P. destruct r. inversion P.
   inversion H. exact (StopMessage, justStop).   Defined.         
  Check fst.
  Check snd.        
  Theorem myhelper : forall parms1 parms2, forall p : (getAction parms1 = ASend), IsValid (getprotocol parms1) (getprotocol parms2) -> IsValid (Send (fst (whatsthatmessage parms1 p)) (getprotocol (snd (whatsthatmessage parms1 p)))) (getprotocol parms2) . intros.  destruct parms1, parms2.
  destruct n. simpl. simpl in p. subst.
  simpl. simpl in H. exact H.
  simpl in p. subst. simpl. simpl in H.
   destruct p0, r, r0, l. simpl.   simpl_eq. simpl in H.
   assumption. simpl. simpl in H. assumption.
   simpl. simpl in H. assumption.
   simpl. simpl in H. assumption.
   simpl. simpl_eq. SearchAbout eq_refl. Abort.
 (*
  Theorem mylittlepony : forall  n m pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  IsValid 
    (getProtocol (S n) ASend pp1 rls1 un1 ls1) 
    (getProtocol ( m) AReceive pp2 rls2 un2 ls2) -> pp1' rls1' un1' ls1', IsValid (Send mess (getProtocol n AReceive pp1' rls1' un1' ls1' ))
(getProtocol (m) AReceive pp2 rls2 un2 ls2) .
intros. destruct mess.  simpl in H. destruct (canSend ls1 pp1). eapply H.   simpl in H.  simpl. protosimpler. destruct mess. 
destruct (reduceUnresolved d m0 un2). proto     induction H.  
  Proof. intro. induction
  *)
  (*
  Theorem IsValidHelper :  forall  n m a2 pp1 pp2 rls1 rls2 un1 un2 ls1 ls2  ,
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2)
  -> exists mess,
  IsValid (Send mess (getProtocol (n) AReceive pp1 rls1 un1 (tl ls1))) (getProtocol (m) a2 pp2 rls2 un2 ls2).
  Proof. intros. simpl in H. destruct (canSend ls1 pp1).
  exists (Sendable_Measurement d (measure d)). 
  apply H.    induction H.  induction n.
  
  
*)   
  *)
  Theorem gimmeNOT : forall (T : Type), forall a : T, a <> a -> False.
  intros. unfold not in H. apply H. reflexivity. Qed. 
  
  Hint Resolve gimmeNOT.      

  Ltac not := match goal with
   | [ H : ?x <> ?x |- _ ] => exfalso; apply gimmeNOT in H; assumption
   end. 
  Theorem IsValid_0_all : forall   m a1 a2 pp1 pp2 rls1 rls2 un1 un2 ls1 ls2  ,
  a1 <> a2 ->
  IsValid (getProtocol ( 0) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2).
  
  Proof.  intros. simpl. destruct a1, a2. not.   auto.
  destruct m. simpl. protosimpler. simpl.
  destruct (canSend ls2 pp2). protosimpler. destruct rls2. protosimpler.
  destruct r. protosimpler. not. Qed.
  Hint Resolve IsValid_0_all.
  
  
  Ltac destr := match goal with
   | [ |- context[ match ?x with 
            | Sendable_Measurement d x => _
            | RequestS x => _
            | StopMessage => _
            end]
                  ] => destruct x
   | [ |- context[(match ?x with 
            | Some _=> _
            | None => _
            end
                )  ]] => destruct x
   | [ |- context[(match ?x with 
            | emptyRequestLS =>_
            | ConsRequestLS _ _ => _
                      end
                )  ]] => destruct x
   | [ |- context[(match ?x with 
            | requestItem _ _ => _ end
                )  ]] => destruct x
   | [ |- context[(let (_, _) := handleRequest ?xg ?yg in _) ] ]=> destruct (handleRequest xg yg)
   | [ |- context[(let (_, _) := ?gh in _) ] ]=> destruct gh
                             
   end. 
  Theorem IsValid_1_all : forall   m a1 a2 pp1 pp2 rls1 rls2 un1 un2 ls1 ls2  ,
  a1 <> a2 ->
  IsValid (getProtocol ( 1) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2).
  
  Proof.  intros. destruct a1, a2. not.  
  simpl. destr.  
  destruct m. simpl. protosimpler. simpl.
  protosimpler. destr. destruct m. simpl.
  protosimpler. simpl. destr. protosimpler.
  destr. protosimpler. destr. protosimpler. protosimpler.
  destr. auto. destr. destruct m. simpl. protosimpler.
  simpl. protosimpler. destr. destr. destr. protosimpler. protosimpler.
  protosimpler.
  simpl. destruct m. simpl. auto. simpl. destr. protosimpler.
  destr. destruct m. protosimpler. protosimpler. destruct m. auto. auto.
  destr. auto. destr. protosimpler. destr. destr. destr. destruct m. simpl. protosimpler.
  simpl. protosimpler. destr. destruct m. protosimpler. simpl. destr. protosimpler.
  destr. protosimpler. destr. protosimpler. protosimpler.
  destruct m. protosimpler. protosimpler. destr. destr. destr. protosimpler.
  protosimpler. protosimpler. auto. not. Qed.
  Hint Resolve IsValid_1_all.
  
  Theorem IsValid_2_all : forall   m a1 a2 pp1 pp2 rls1 rls2 un1 un2 ls1 ls2  ,
  a1 <> a2 ->
  IsValid (getProtocol ( 2) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2).
  
  Proof.  intros. destruct a1, a2. not.
  induction m. auto.
  simpl. destr. protosimpler.
  destr. destruct m. auto.
  simpl. destr. protosimpler. destr. auto. auto.
  destr. auto. destr. protosimpler. destr. destr. destr. destruct m.
  simpl. protosimpler. protosimpler. destr. destruct m. protosimpler. simpl.
  protosimpler. destr. protosimpler. destr. protosimpler. destr.
  protosimpler. protosimpler. destruct m. protosimpler. protosimpler. destr. destr.
  destr. protosimpler. protosimpler. protosimpler. protosimpler. auto.
  destr. auto. destr. protosimpler. destr. destr. destr. protosimpler. destr. auto. auto.
  protosimpler. destr. destr. destr. destruct m. protosimpler. protosimpler. destr. destruct m.
  protosimpler. simpl. destr. protosimpler. protosimpler. protosimpler.
  destruct m. protosimpler. protosimpler. destr. destr. destr. protosimpler. protosimpler.
  protosimpler. auto.
  auto.
  destruct m. auto.
  simpl. protosimpler. destr. protosimpler. destr. destr. destruct m.
  auto. protosimpler. protosimpler. destr. destruct m. protosimpler.
  simpl. destr. protosimpler. destr. protosimpler. destr. protosimpler.
  protosimpler. destr. auto. destr. destruct m. protosimpler.
  protosimpler. destr. destr. destr. protosimpler. protosimpler. protosimpler.
  protosimpler. destr.  destr. auto.
   destr.  protosimpler. destr. destr. destr. destr. protosimpler. destruct m.
   protosimpler. protosimpler. destr. destruct m. protosimpler. simpl.
   destr. protosimpler. destr. protosimpler. protosimpler.
   destr. auto. destr. protosimpler. destr. destr. destr. destruct m. protosimpler. protosimpler.
   destr. destruct m. protosimpler. simpl. destr. protosimpler. destr.     protosimpler.
   destr. protosimpler. protosimpler. destruct m. protosimpler. protosimpler.
   destr. destr. destr. protosimpler. protosimpler. protosimpler. protosimpler.
   auto. destruct m. protosimpler. protosimpler. destr. destr. destr. protosimpler.
   destr. auto. auto. protosimpler. destr. destr. destr. destruct m. protosimpler.
   protosimpler. destr. destruct m. protosimpler. simpl. destr.    protosimpler. 
   protosimpler. protosimpler. destruct m. protosimpler. protosimpler.
   destr. destr. destr. protosimpler. protosimpler. protosimpler. protosimpler.
   auto. auto. destr. auto. destr. destr. protosimpler. destr. destr. destr.
   destr. destruct m. protosimpler. protosimpler. destr. destruct m. protosimpler.
   simpl. destr. protosimpler. destr. protosimpler. protosimpler.
   destr. auto. destr. protosimpler. destr. destr. destr.
   destruct m. protosimpler. protosimpler. destr. destruct m.
   protosimpler. simpl. destr. protosimpler. destr. protosimpler.
   destr. protosimpler. protosimpler. destruct m. protosimpler. protosimpler.
   destr. destr. destr. protosimpler. protosimpler. protosimpler. protosimpler. protosimpler.
   destruct m. protosimpler.   protosimpler. destr. destr. destr. protosimpler.
   destr. auto. auto. protosimpler. destr. destr. destr. destruct m.
   protosimpler. protosimpler. destr. destruct m. protosimpler. simpl.
   destr. protosimpler. protosimpler.    protosimpler. destruct m.
   protosimpler. protosimpler. destr. destr. destr. protosimpler.
   protosimpler. protosimpler. protosimpler.
   auto. auto.
   not.
   Qed.  
   
  
  Hint Resolve IsValid_2_all.
  
  
  Ltac search_prem tac :=
  let rec search P :=
    tac
    || (simpl; tac)
    || match P with
         | ?P1 /\ ?P2 =>
           (simpl; search P1)
           || (simpl; search P2)
       end
  in match goal with
       | [ |- ?P /\ _ -> _ ] => search P
       | [ |- _ /\ ?P -> _ ] => simpl; search P
       | [ |- _ -> _ ] => progress (tac || (simpl; tac))
     end.
   Ltac doesSomething tac := progress (repeat tac).
    
   Ltac myCrush' := match goal with _ => 
   (progress (repeat 
              (progress
                 (doesSomething simpl || 
                  doesSomething not || 
                  doesSomething protosimpler || 
                  doesSomething auto || 
                  doesSomething destr
                      )
              ) 
            )) || (repeat destr) end . 
   Ltac myCrush := (progress myCrush') || match goal with 
      | [m : nat |- IsValid _ _ ] => (destruct m)
      end.  
      
      (*
   Theorem IsValid_3_all : forall   m a1 a2 pp1 pp2 rls1 rls2 un1 un2 ls1 ls2  ,
  a1 <> a2 ->
  IsValid (getProtocol ( 3) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2).
  
  Proof.  intros. destruct a1, a2. myCrush.
  induction m; [myCrush | myCrush]. myCrush. myCrush. myCrush.
  myCrush. myCrush. myCrush.
  myCrush. myCrush. myCrush.
  destruct m; [myCrush | myCrush].
  myCrush; myCrush; myCrush; myCrush; myCrush; myCrush; myCrush; myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush. myCrush.
Qed.

 Theorem IsValid_4_all : forall   m a1 a2 pp1 pp2 rls1 rls2 un1 un2 ls1 ls2  ,
  a1 <> a2 ->
  IsValid (getProtocol ( 4) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2).
  
  Proof.  intros. destruct a1, a2; repeat myCrush. 
  Qed.
  
 Theorem IsValid_5_all : forall   m a1 a2 pp1 pp2 rls1 rls2 un1 un2 ls1 ls2  ,
  a1 <> a2 ->
  IsValid (getProtocol ( 5) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2).
  
  Proof.  intros. destruct a1, a2; repeat myCrush. 
  Qed.
  
  
  
  Theorem IsValid_6_all : forall   m a1 a2 pp1 pp2 rls1 rls2 un1 un2 ls1 ls2  ,
  a1 <> a2 ->
  IsValid (getProtocol ( 6) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2).
  
  Proof.  intros. destruct a1, a2; repeat myCrush. 
  Qed.
   *)
   
   
   Ltac ph := match goal with
 |  [ H : IsValid (Send ?M ?X) (Receive ?F) |- _ ] => 
           apply @lr_send with (F M) in H
 | _ => idtac "fail"          end. (* 
  | IsValid (Receive ?F) (Send ?M ?X) => 
           apply @rl_send with (F M)
  | IsValid Stop Stop  => 
           apply  both_stop
  | IsValid Stop  (Send StopMessage Stop) => 
           apply lr_stop
  | IsValid (Send StopMessage Stop) Stop => 
           apply rl_stop
  end.*)
  Theorem IsValid_awanySucc : forall  n a1  pp1  rls1  un1  ls1 protocol  ,
  IsValid (getProtocol (S n ) a1 pp1 rls1 un1 ls1) protocol -> 
    IsValid (getProtocol (n) a1 pp1 rls1 un1 ls1) protocol.
    Proof. intros. inversion H. subst. destruct a1. destruct (canSend ls1 pp1).
    inversion H1. destruct rls1. inversion H1. destruct r. inversion H1. inversion H1.
    destruct a1. destruct (canSend ls1 pp1). inversion H1. destruct rls1.
    
    destruct n. auto.
    subst. simpl in H. destruct (canSend ls1 pp1). inversion H.
    simpl. destruct (canSend ls1 pp1).                     simpl in H. inversion H.    destruct a1. subst.       induction n. intros. inversion H.  simpl.  auto.     
  Proof. intro. induction n. intros. apply Is
  Theorem IsValid_asdf : forall  n m a1 a2 pp1 pp2 rls1 rls2 un1 un2 ls1 ls2  ,
  a1 <> a2 ->
  IsValid (getProtocol (n ) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2)
  ->forall z pp2' rls2' un2' ls2',  
    IsValid (getProtocol (n) a1 pp1 rls1 un1 ls1) (getProtocol (z) a2 pp2' rls2' un2' ls2').
  Proof. intro. induction n. intros. apply IsValid_0_all. assumption.
  intros. destruct a1,a2. not.  simpl. destr. destruct z. myCrush. simpl.
  protosimpler. destr. eapply IHn. auto. auto.
  auto.
  destr. auto. destr. destruct z. myCrush. protosimpler. destr. destr. destr.
                 
  destr.  
    protosimpler.  auto.     
  simpl. destr. destr.   myCrush. myCrush.    
   Theorem IsValid_pred_All : forall  n m a1 a2 pp1 pp2 rls1 rls2 un1 un2 ls1 ls2  ,
  a1 <> a2 ->
  IsValid (getProtocol (S n ) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2)
  -> IsValid (getProtocol (n ) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2).
  Proof. intro. destruct n. intros. apply IsValid_0_all. assumption.
  
  intros. destruct a1,a2; myCrush.  inversion H0. myCrush. inversion H2. auto.
  inversion H2. destr. myCrush. simpl in H3. inversion H3. simpl in H3. inversion H3.
  destruct m; (inversion H3). destruct m. simpl in H3. inversion H3. simpl in H3.
  inversion H3. destr. protosimpler. destruct m. simpl in H2. inversion H2. 
  auto. simpl in H2. inversion H2.       inversion H2. subst.              myCrush.   auto.      myCrush. myCrush. myCrush. myCrush. dest destr.  myCrush.    eqn:eifje. auto.  
  destruct a1,a2. not. simpl in H0.   destruct (canSend ls1 pp1). destruct m.
  apply IsValid_IsValid.
  apply IsValid_0_all. auto.
  
  Check @lr_send. simpl in H0.
  destruct H0. 
  match H0 with 
  | (IsValid (Send ?M ?X) (Receive ?F)) => 
           apply @lr_send with (F M) in H
  | _ => idtac "fail"
  end. 
  ph. 
   proto' H0.   
  apply @lr_send with (m:= (Sendable_Measurement d (measure d)))(f := (
             (fun m : Message =>
              match m with
              | Sendable_Measurement d v =>
                  match reduceUnresolved d v un1 with
                  | Some newUnresolvedState => getProtocol n ASend (reducePrivacy d v pp1) rls1 newUnresolvedState (tl ls1)
                  | None => Send StopMessage Stop
                  end
              | RequestS d =>
                  let (p, reqItem) := handleRequest pp1 d in
                  let (newpp, mess) := p in
                  match mess with
                  | Sendable_Measurement _ _ => Send mess (getProtocol n AReceive newpp emptyRequestLS (ConsRequestLS reqItem un1) (tl ls1))
                  | RequestS _ => Send mess (getProtocol n AReceive newpp emptyRequestLS (ConsRequestLS reqItem un1) (tl ls1))
                  | StopMessage => Send StopMessage Stop
                  end
              | StopMessage => Stop
              end))) in H0. 
  simpl in H0.      
  simpl in H0. 
  eapply IHn.     myCrush.    destruct a1, a2. not. destruct n,m. myCrush.
  myCrush.
  apply IsValid_IsValid. apply IsValid_0_all. auto.
  myCrush. myCrush. myCrush. myCrush.   
  simpl.   
  simpl. 
  myCrush.       inversion H0. destruct n. myCrush.  inversion H2.  inversion H2.
  destruct (canSend ls1 pp 
 Theorem IsValid_succ_all : forall  n m a1 a2 pp1 pp2 rls1 rls2 un1 un2 ls1 ls2  ,
  a1 <> a2 ->
  IsValid (getProtocol ( n ) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2)
  -> IsValid (getProtocol (S n ) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2).
  Proof. intros. destruct a1, a2. not.   inversion H0. destruct n. inversion H2.  inversion H2.
  destruct (canSend ls1 pp1). inversion H4. destruct rls1. inversion H4.
  destruct r. inversion H4. destruct m. inversion H3. inversion H3.
  destruct n. inversion H2. inversion H2. destruct (canSend ls1 pp1).
  inversion H4. destruct rls1. inversion H4. destruct r. inversion H4.
  subst. simpl. Abort.
  
   Theorem pony : forall (n m : nat) (a1 a2 : Action) (pp1 pp2 : PrivacyPolicy) (rls1 rls2 un1 un2 : RequestLS)
        (ls1 ls2 : list Description),
      a1 <> a2 -> IsValid (getProtocol n a1 pp1 rls1 un1 ls1) (getProtocol (S m) a2 pp2 rls2 un2 ls2) -> exists  a1' a2' pp1' pp2' rls1' rls2' un1' un2' ls1' ls2' mess, 
       IsValid (getProtocol n a1' pp1' rls1' un1' ls1') (Send mess (getProtocol m a2' pp2' rls2' un2' ls2')).
   Proof. intros. destruct a1,a2. not. simpl in H0.
    Abort.
    
    Theorem IsValidSupreme : forall  n m a1 a2 pp1 pp2 rls1 rls2 un1 un2 ls1 ls2  ,
  a1 <> a2 ->
  IsValid (getProtocol ( n) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2).
  Proof.  intro. induction n.
  (* n = 0 case *)
   intros. auto. intros.
   simpl. destruct a1,a2; myCrush. myCrush.      myCrush. myCrush. myCrush.
   apply IHn. auto.
   auto. auto.
   myCrush. myCrush. myCrush. myCrush.
   destruct n. myCrush. myCrush.
   repeat destr. simpl in IHn.
     apply IHn.   .   
   
   myCrush.
    muCrush.        
   destr.  
   repeat destr. 
   myCrush.     destruct m.
     (* m = 0 case *)
      destruct a1,a2. elim H; trivial.
      apply IsValid_zero.
      apply IsValid_IsValid. apply IsValid_zero.
      elim H; trivial.
     (* m = S m  case *)
       destruct a1,a2. 
          elim H; trivial.
          proto_simpler. proto_simpler. auto. auto.
          proto_simpler. destruct ls2. simpl. destruct rls2. protosimpler.
          destruct r. protosimpler. sendstop. simpl.
          destruct pp2. simpl. destruct rls2. protosimpler.
          destruct r. protosimpler. sendstop.
          destruct d. simpl. simpl_eq. destruct (eq_dec_Description d0 (descriptor d)). simpl. destruct r. destruct rls2. protosimpler . destruct r0. protosimpler.
          sendstop. protosimpler. sendstop. destruct rls2. protosimpler.
          destruct r. protosimpler. sendstop. destruct rls2. protosimpler.
          destruct r. protosimpler. sendstop. destruct rls2. protosimpler.
          destruct r. protosimpler. sendstop.
          destruct pp2. simpl. destruct rls2. protosimpler.
          destruct r0. protosimpler. sendstop. simpl.      sendstop.    
           destruct rls2. protosimpler.
          destruct r. protosimpler. sendstop. destruct rls2. protosimpler.
          destruct r. protosimpler. sendstop. destruct rls2. protosimpler.
          destruct r. protosimpler. sendstop. 
          sendstop.              .     sendstop.       apply IsValid_zero.   destruct m.  proto_simpler. proto_simpler. proto_simpler.
          auto. auto. auto. proto_simpler. proto_simpler. proto_simpler. 
          auto. auto. auto.
          (* receive receive *)
          elim H; trivial.              
   (* n = S n' case *)
       
    intros. destruct a1. destruct a2.  elim H; trivial.
     (* send receive *)
     proto_simpler.
     destruct (canSend ls1 pp1).  
      destruct m. protosimpler. sendstop.
      protosimpler. 
         destruct (reduceUnresolved d (measure d) un2). apply IHn.
         unfold not. intros. inversion H0.
         sendstop.
         destruct rls1. sendstop.
         destruct r.
         destruct m. protosimpler. sendstop.
         simpl. protosimpler.
         destruct (handleRequest pp2 d). destruct p.
         destruct m0.        
         specialize IHn with (m:= (S m)) (a1 := AReceive) (a2:= ASend).
         simpl in IHn.
         specialize IHn with (pp1:=pp1) (pp2:=pp2).
         eapply IHn.   
         eapply IHn. 
         simpl in IHn. 
         
         destruct n. repeat proto_simpler. destruct m. repeat proto_simpler.
         repeat proto_simpler.     auto.   simpl.  
         specialize IHn with (m:= (S m)) (a1 := AReceive) (a2:= ASend).
         
         destruct n. repeat proto_simpler.      
         simpl in IHn. 
         pH IHn. 
         simpl in IHn. eapply IHn.   
         destruct n. proto_simpler. proto_simpler. destruct m. proto_simpler.
         proto_simpler. auto. auto. proto_simpler. proto_simpler. auto. auto. auto.
         proto_simpler. proto_simpler.  
         destruct (eq_dec_Description d d0). destruct r. subst. simpl.
         destruct ((if b m0 then Some un1 else None)) .
         specialize IHn with (m:= (S m)) (a2:= AReceive).         .         trivial.   
     destruct m
     (* m = 0 case *).  proto_simpler. proto_simpler. destruct n.
        proto_simpler. proto_simpler. auto. auto.
        proto_simpler. proto_simpler. auto. auto. auto.
        proto_simpler. proto_simpler. 
        destruct (reduceUnresolved d (measure d) un2).
        eapply IsValid_IsValid in IHn. .  in IHn.  
        destruct rls1. proto_simpler. auto. auto.
        destruct r. proto_simpler. destruct n.
        proto_simpler. proto_simpler. auto. auto.
        proto_simpler. proto_simpler. auto. auto. auto.
        proto_simpler.
        destruct (canSend ls1 pp1). proto_simpler. destruct n.
        proto_simpler. destruct (reduceUnresolved d (measure d) un2).
        destruct m. proto_simpler. proto_simpler. auto. auto. proto_simpler.
        destruct (canSend ls2 (reducePrivacy d (measure d) pp2)).
        proto_simpler. destruct m. proto_simpler. proto_simpler. auto. auto.
        proto_simpler. proto_simpler. auto. auto. auto.
        destruct rls2. proto_simpler. auto. auto.
        destruct r0. proto_simpler. destruct m.
        proto_simpler. proto_simpler. auto. auto.
        proto_simpler. proto_simpler. auto. auto. auto.
        proto_simpler. auto. auto.
        destruct (reduceUnresolved d (measure d) un2). destruct m.
        proto_simpler. proto_simpler. auto. auto. proto_simpler.
        destruct (canSend ls2 (reducePrivacy d (measure d) pp2)).
        proto_simpler. destruct (reduceUnresolved d0 (measure d0) un1).   
        proto_simpler. 
        assumption.         
         eapply IHn.  
        subst. 
        eapply IHn0. 
                         .   
       
   
  Theorem IsValidSupreme : forall  n m a1 a2 pp1 pp2 rls1 rls2 un1 un2 ls1 ls2  ,
  a1 <> a2 ->
  IsValid (getProtocol ( n) a1 pp1 rls1 un1 ls1) (getProtocol (m) a2 pp2 rls2 un2 ls2).
  Proof. intro. induction n.
  (* n = 0 case *)
   intros. destruct m.
     (* m = 0 case *)
      destruct a1,a2. elim H; trivial.
      apply IsValid_zero.
      apply IsValid_IsValid. apply IsValid_zero.
      elim H; trivial.
     (* m = S m  case *)
       destruct a1,a2. 
          elim H; trivial.
          proto_simpler. proto_simpler. auto. auto.
          proto_simpler. destruct (canSend ls2 pp2).  proto_simpler.
           sendstop. auto.
          destruct rls2. proto_simpler. auto. auto.
          destruct r. destruct m.  proto_simpler. proto_simpler. proto_simpler.
          auto. auto. auto. proto_simpler. proto_simpler. proto_simpler. 
          auto. auto. auto.
          (* receive receive *)
          elim H; trivial.              
   (* n = S n' case *)
       
    intros. destruct a1. destruct a2.  elim H; trivial.
     (* send receive *)
     proto_simpler.
     destruct (canSend ls1 pp1).  
      destruct m. protosimpler. sendstop.
      protosimpler. 
         destruct (reduceUnresolved d (measure d) un2). apply IHn.
         unfold not. intros. inversion H0.
         sendstop.
         destruct rls1. sendstop.
         destruct r.
         destruct m. protosimpler. sendstop.
         simpl. protosimpler.
         destruct (handleRequest pp2 d). destruct p.
         destruct m0.        
         specialize IHn with (m:= (S m)) (a1 := AReceive) (a2:= ASend).
         simpl in IHn.
         specialize IHn with (pp1:=pp1) (pp2:=pp2).
         eapply IHn.   
         eapply IHn. 
         simpl in IHn. 
         
         destruct n. repeat proto_simpler. destruct m. repeat proto_simpler.
         repeat proto_simpler.     auto.   simpl.  
         specialize IHn with (m:= (S m)) (a1 := AReceive) (a2:= ASend).
         
         destruct n. repeat proto_simpler.      
         simpl in IHn. 
         pH IHn. 
         simpl in IHn. eapply IHn.   
         destruct n. proto_simpler. proto_simpler. destruct m. proto_simpler.
         proto_simpler. auto. auto. proto_simpler. proto_simpler. auto. auto. auto.
         proto_simpler. proto_simpler.  
         destruct (eq_dec_Description d d0). destruct r. subst. simpl.
         destruct ((if b m0 then Some un1 else None)) .
         specialize IHn with (m:= (S m)) (a2:= AReceive).         .         trivial.   
     destruct m
     (* m = 0 case *).  proto_simpler. proto_simpler. destruct n.
        proto_simpler. proto_simpler. auto. auto.
        proto_simpler. proto_simpler. auto. auto. auto.
        proto_simpler. proto_simpler. 
        destruct (reduceUnresolved d (measure d) un2).
        eapply IsValid_IsValid in IHn. .  in IHn.  
        destruct rls1. proto_simpler. auto. auto.
        destruct r. proto_simpler. destruct n.
        proto_simpler. proto_simpler. auto. auto.
        proto_simpler. proto_simpler. auto. auto. auto.
        proto_simpler.
        destruct (canSend ls1 pp1). proto_simpler. destruct n.
        proto_simpler. destruct (reduceUnresolved d (measure d) un2).
        destruct m. proto_simpler. proto_simpler. auto. auto. proto_simpler.
        destruct (canSend ls2 (reducePrivacy d (measure d) pp2)).
        proto_simpler. destruct m. proto_simpler. proto_simpler. auto. auto.
        proto_simpler. proto_simpler. auto. auto. auto.
        destruct rls2. proto_simpler. auto. auto.
        destruct r0. proto_simpler. destruct m.
        proto_simpler. proto_simpler. auto. auto.
        proto_simpler. proto_simpler. auto. auto. auto.
        proto_simpler. auto. auto.
        destruct (reduceUnresolved d (measure d) un2). destruct m.
        proto_simpler. proto_simpler. auto. auto. proto_simpler.
        destruct (canSend ls2 (reducePrivacy d (measure d) pp2)).
        proto_simpler. destruct (reduceUnresolved d0 (measure d0) un1).   
        proto_simpler. 
        assumption.         
         eapply IHn.  
        subst. 
        eapply IHn0. 
                         .   
       
       intros.   
       (* n side is sending, what can we send? *) destruct ls1 eqn:ls1case. simpl.  
       simpl. destruct rls1 eqn :rls1case.   proto_simpler. proto_simpler. auto. auto.
  destruct r. proto_simpler. proto_simpler.
  destruct (handleRequest pp2 d). destruct p. destruct m0.
  proto_simpler.  auto. auto.  proto_simpler.          
  destruct (canSend ls1 pp1). proto_simpler. destruct (reduceUnresolved d (measure d) un2).
  destruct (canSend ls2 (reducePrivacy d (measure d) pp2)). proto_simpler.       proto_simpler.            apply IsValid_zero. intros. simpl.  simpl.
  destruct (canSend ls1 pp1). progress proto_simpler. 
    destruct (reduceUnresolved d (measure d) un2). apply IsValid_IsValid. apply IHn.
    destruct n. proto_simpler. proto_simpler. auto. auto.
    proto_simpler. proto_simpler. auto. auto. proto_simpler.
    destruct rls1.  proto_simpler. auto. auto. destruct r.  proto_simpler.
    destruct (handleRequest pp2 d). destruct p. destruct m.  proto_simpler.  proto_simpler.  
    destruct n. proto_simpler. proto_simpler. auto. auto.
    proto_simpler. proto_simpler. auto. auto. proto_simpler.
    destruct rls1.  proto_simpler. auto. auto. destruct r.  proto_simpler.
    destruct n.             
    proto_simpler.    
  destruct ( canSend ls2 (reducePrivacy d (measure d) pp2)).
  proto_simpler.  
  
  
  Theorem IsValidevverything : forall  n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2 ,
  IsValid (getProtocol ( n) ASend pp1 rls1 un1 ls1) (getProtocol (n) AReceive pp2 rls2 un2 ls2).
  Proof. intro. induction n. intros.  apply IsValid_zero. intros. simpl.  simpl.
  destruct (canSend ls1 pp1). progress proto_simpler. 
    destruct (reduceUnresolved d (measure d) un2). apply IsValid_IsValid. apply IHn.
    destruct n. proto_simpler. proto_simpler. auto. auto.
    proto_simpler. proto_simpler. auto. auto. proto_simpler.
    destruct rls1.  proto_simpler. auto. auto. destruct r.  proto_simpler.
    destruct (handleRequest pp2 d). destruct p. destruct m.  proto_simpler.  proto_simpler.  
    destruct n. proto_simpler. proto_simpler. auto. auto.
    proto_simpler. proto_simpler. auto. auto. proto_simpler.
    destruct rls1.  proto_simpler. auto. auto. destruct r.  proto_simpler.
    destruct n.             
    proto_simpler.    
  destruct ( canSend ls2 (reducePrivacy d (measure d) pp2)).
  proto_simpler.  
  destruct (reduceUnresolved d0 (measure d0) un1). Print succValid. 
  apply succValid. apply IHn.
  apply sendStopAll. auto. 
  destruct rls2. proto_simpler. auto. auto. 
  destruct r0. proto_simpler. destruct (handleRequest pp1 d0). destruct p.
  destruct m.     proto_simpler. auto  apply sendStopAll.    
  (* Stop message *)
  destruct n. proto_simpler. proto_simpler.  auto. auto.
  simpl. proto_simpler. auto. auto.
  destruct (reduceUnresolved d0 (measure d0) un1). auto. auto.  
  destruct rls2. proto_simpler. auto. auto. destruct r0. proto_simpler. 
  destruct (handleRequest pp1 d0). destruct p. destruct m.
  (*Sendable measurment) *)
  destruct n. proto_simpler. proto_simpler. apply IsValid_IsValid. apply  IguessThatsOkay.   auto.
  simpl_eq. proto_simpler. 
  destruct (eq_dec_Description d0 d1). simpl_eq.  
  destruct r0. destruct ( b
        (eq_rect d1 (fun y : Description => measurementDenote y) m d0
           (eq_sym e))). subst.  simpl_eq. simpl_eq. simpl_JMeq. simpl_eqs. simplify_eqs.
  simplify_IH_hyps . autounfold. simplify_eqs.
  destruct ( b (eq_rect d1 (fun y : Description => measurementDenote y) m d0 eqH) ) .
  subst. 
      elim_eq_rect.  simpl_eq.    simpl_uip.  apply ProofIrrelevance.   elim_eq_rect.  simpl_eq.  
  destruct (reduceUnresolved d0 (measure d0) un1). auto. auto.  
  destruct rls2. proto_simpler. auto. auto. destruct r0. proto_simpler. 
  destruct (handleRequest pp1 d0). destruct p. destruct m.
  (*Sendable measurment) *)
                    eauto.   proto_simpler.  assumption.   
     eapply IHn.   proto_simpler   proto_simpler. destruct (canSend ls1 pp1). proto_simpler. destruct (reduceUnresolved d (measure d) un2).
     
   
Theorem IsValid_succ : forall  pp1 pp2 rls1 rls2 un1 un2 ls1 ls2 n,
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n) AReceive pp2 rls2 un2 ls2) -> 
  IsValid (getProtocol n ASend pp1 rls1 un1 ls1) (getProtocol  n AReceive pp2 rls2 un2 ls2).
  Proof. intro. intro. intro. intro. intro. intro. intro. intro. intro.
  simpl.
  destruct (canSend ls1 pp1). intros.  inversion H. subst. apply rl_send in H.    in H. .  .  proto_simpler.    apply proto_simpler.       intros. simpl in H. .  induction (n). apply IsValid_zero. .    

Theorem IsValid_inc : forall  pp1 pp2 rls1 rls2 un1 un2 ls1 ls2 n,
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n) AReceive pp2 rls2 un2 ls2) -> 
  IsValid (getProtocol (S (S n)) ASend pp1 rls1 un1 ls1) (getProtocol (S (S n)) AReceive pp2 rls2 un2 ls2).
  Proof.
  intros. proto_simpler. 
  destruct (canSend ls1 pp1). proto_simpler. 
  destruct (reduceUnresolved d (measure d) un2). 
  destruct (canSend ls2 (reducePrivacy d (measure d) pp2)).
  proto_simpler. destruct (reduceUnresolved d0 (measure d0)).
  simpl in H.    simpl    


Theorem IsValid_inc : forall  pp1 pp2 rls1 rls2 un1 un2 ls1 ls2 n,
  IsValid (getProtocol n ASend pp1 rls1 un1 ls1) (getProtocol n AReceive pp2 rls2 un2 ls2) -> 
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n) AReceive pp2 rls2 un2 ls2).
  intro. intro. intro. intro. intro. intro. intro. intro. intro.
  induction n. intros. proto_simpler. destruct (canSend ls1 pp1). proto_simpler. destruct (reduceUnresolved d (measure d) un2).
  proto_simpler. auto. auto. proto_simpler. auto. auto.
  destruct (reduceUnresolved d (measure d) un2). auto. auto.
  destruct rls1. proto_simpler. auto. auto.
  destruct r. proto_simpler. destruct (handleRequest pp2 d). destruct p. destruct m.
  proto_simpler. auto. 
  
  apply IguessThatsOkay.
  
  auto.
  proto_simpler.
  
  apply IguessThatsOkay.
  
  auto. proto_simpler. auto. auto.           
  destruct (handleRequest pp2 d).
  destruct p.
  destruct m. auto.
  auto. auto.      

Theorem IsValid_inc2 : forall  pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  IsValid (getProtocol 2 ASend pp1 rls1 un1 ls1) (getProtocol 2 AReceive pp2 rls2 un2 ls2).
  Proof. intros. simpl. destruct (canSend ls1 pp1). proto_simpler. proto_simpler.
  destruct (reduceUnresolved d (measure d) un2). 
  destruct (canSend ls2 (reducePrivacy d (measure d) pp2)). proto_simpler.
  destruct (reduceUnresolved d0 (measure d0) un1). auto. auto.
  destruct (reduceUnresolved d0 (measure d0) un1). auto. auto.
  destruct rls2. proto_simpler. auto. auto.
  destruct r0.   proto_simpler. destruct (handleRequest pp1 d0). destruct p.
  destruct m. admit. admit. auto.       
  destruct (handleRequest pp1 d0). destruct p. destruct m. auto. auto. auto.
  proto_simpler. auto. auto.
  destruct (reduceUnresolved d (measure d)  un2).
  destruct (canSend ls2 (reducePrivacy d (measure d) pp2)). auto.
  destruct rls2. auto.
  destruct r0. auto. auto.
  destruct rls1. proto_simpler. proto_simpler. auto. auto.
  destruct r. proto_simpler. proto_simpler.      
  destruct (handleRequest pp2 d). destruct p.   
  destruct m. proto_simpler.   
  destruct (eq_dec_Description d d0). destruct r. simpl_eq. subst. eauto. simpl_eq.
  auto. auto. proto_simpler. auto. auto. proto_simpler. auto. auto.
  proto_simpler. auto. auto.
  proto_simpler. auto. auto.
  proto_simpler. auto. auto.
  proto_simpler. auto. auto. auto.
  destruct rls2. eauto.
  destruct r0. proto_simpler.    
  destruct (handleRequest pp1 d0). destruct p. destruct m.
  proto_simpler. admit. auto. proto_simpler. admit. auto. proto_simpler. auto. auto.
  destruct (handleRequest pp1 d0). destruct p. destruct m. auto. auto.
  auto. proto_simpler. auto. auto.
  destruct (reduceUnresolved d (measure d) un2).
  destruct (canSend ls2 (reducePrivacy d (measure d) pp2)). auto.
  destruct rls2. auto. destruct r0. auto. auto.
  destruct rls1. eauto.
  destruct r. proto_simpler. proto_simpler.
  destruct (handleRequest pp2 d). destruct p. destruct m. proto_simpler.    
  destruct (eq_dec_Description d d0). destruct r. subst. simpl.
  destruct (b m). proto_simpler. auto. auto. proto_simpler. auto. auto. destruct (reduceUnresolved d0 m un1). proto_simpler. auto. auto. proto_simpler. auto.
  auto. destruct (eq_dec_Description d d0). destruct r. subst. simpl.
  destruct (b m). auto.    auto. destruct (reduceUnresolved d0 m un1). auto. auto. proto_simpler. destruct (handleRequest pp1 d0). destruct p0. destruct m.
  proto_simpler. destruct r0. destruct (eq_dec_Description d2 d1).
  destruct r0. subst. simpl. destruct (b m). eauto. eauto.
  destruct (reduceUnresolved d1 m un2). eauto. eauto.
  destruct r0. destruct (eq_dec_Description d2 d1). destruct r0.
  subst. simpl. (destruct (b m)). auto. auto. destruct (reduceUnresolved d1 m un2). auto. proto_simpler. proto_simpler. destruct (handleRequest p d1). destruct p1.
  destruct m. proto_simpler. admit. auto.
  proto_simpler. admit. auto. proto_simpler. auto. auto.
  destruct (handleRequest p d1). destruct p1. destruct m.
  auto. auto. auto. proto_simpler. auto. auto.
  destruct (handleRequest pp1 d0). destruct p0.
  destruct m. auto. auto. auto. proto_simpler. auto. auto.
   Abort.


  (*lay out what you're tryng to accomplish (goal/ hypo in one sentence)
    like a one page description of my work (2 or 3 maybe)s
    how to merge with Adam.
  
  *)
  (*
Theorem IsValid_AnyPrivacy : forall n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  IsValid (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol (n) AReceive pp2 rls2 un2 ls2) ->
  forall pp1',
  IsValid (getProtocol (n) ASend pp1' rls1 un1 ls1) (getProtocol (n ) AReceive pp2 rls2 un2 ls2).
  Proof. intros. eauto. intros. eapply IHn.       generalize dependent pp2.  induction pp1. destruct n.  simpl. eauto. intros.  simpl. destruct (canSend ls1 EmptyPolicy). intros.
  destruct (canSend ls1 pp1').   proto.
  destruct (reduceUnresolved d0 (measure d0) un2). eauto.         

Theorem IsValid_Pred : forall n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n) AReceive pp2 rls2 un2 ls2) ->
  IsValid (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol (n ) AReceive pp2 rls2 un2 ls2).
  Proof. simpl. intros. induction n. simpl. eauto. simpl.  
      destruct (canSend ls1 pp1). proto. 
  destruct (reduceUnresolved d (measure d) un2). eauto.    
  apply @lr_send with (m :=(Sendable_Measurement d (measure d))) (f :=(fun m : Message =>
          match m with
          | Sendable_Measurement d v =>
              match reduceUnresolved d v un2 with
              | Some newUnresolvedState =>
                  getProtocol n ASend (reducePrivacy d v pp2) rls2
                    newUnresolvedState ls2
              | None => Send StopMessage Stop
              end
          | RequestS d =>
              let (p, reqItem) := handleRequest pp2 d in
              let (newpp, mess) := p in
              match mess with
              | Sendable_Measurement _ _ =>
                  Send mess
                    (getProtocol n AReceive newpp emptyRequestLS
                       (ConsRequestLS reqItem un2) ls2)
              | RequestS _ =>
                  Send mess
                    (getProtocol n AReceive newpp emptyRequestLS
                       (ConsRequestLS reqItem un2) ls2)
              | StopMessage => Send StopMessage Stop
              end
          | StopMessage => Stop
          end)) in H.  in H. simpl in H.   auto in H.  pH H. .  proto in H. .   intros.  
*)
Theorem IsValid_inc : forall n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  IsValid (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol ( n) AReceive pp2 rls2 un2 ls2) ->
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n ) AReceive pp2 rls2 un2 ls2).




Theorem IsValid_inc : forall n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  IsValid (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol ( n) AReceive pp2 rls2 un2 ls2) ->
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n ) AReceive pp2 rls2 un2 ls2).
  Proof. intro. induction n. intros. simpl. destruct (canSend ls1 pp2). destruct (canSend ls1 pp1). proto.
  destruct (reduceUnresolved d0 (measure d0) un2). proto. auto. auto. proto. auto. auto. destruct (reduceUnresolved d0 (measure d0) un2).
  auto. auto. destruct rls1. proto. auto. auto. destruct r. proto .     destruct (handleRequest pp2 d0). destruct p. destruct m. proto. apply IguessThatsOkay. auto.
  proto. apply IguessThatsOkay. auto. proto. auto. auto. destruct (handleRequest pp2 d0). destruct p. destruct m. auto. auto. auto.
  destruct (canSend ls1 pp1). proto. destruct (reduceUnresolved _ _ _). eauto. eauto. auto.
  destruct rls1. eauto. destruct r. proto. destruct (handleRequest _ _). destruct p. destruct m.
  proto. apply IguessThatsOkay. auto. proto. apply IguessThatsOkay. auto. proto. auto. auto.
  intros. eauto.
  (*Case 2 *)
   intros. simpl. destruct (canSend ls1 pp1). proto. destruct (reduceUnresolved d (measure d) un2). 
   destruct (canSend ls2 (reducePrivacy d (measure d) pp2)). proto. 
   destruct (reduceUnresolved d0 (measure d0) un1). eauto.    intros.  Admitted.


Theorem allGood : forall n pp1 pp2 rls1 un1 un2 ls1 ls2,
 IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n) AReceive pp2 emptyRequestLS un2 ls2).
 Proof. intro. induction n. simpl. intros. destruct rls1. destruct (canSend _ _).  proto_simpler. destruct (reduceUnresolved _ _ _).  eauto. eauto. auto.
 proto. auto. auto.  
 destruct r. destruct (canSend ls1 pp1).   proto_simpler. destruct (reduceUnresolved d0 (measure d0)).
proto. destruct (handleRequest pp2 d). auto. auto. eauto. destruct (reduceUnresolved d0 (measure d0) un2). auto. auto.
proto. destruct (handleRequest pp2 d). destruct p. destruct m. proto. apply IguessThatsOkay. auto. proto. apply IguessThatsOkay. auto. proto. auto. auto.
destruct (handleRequest pp2 d). destruct p. destruct m. auto. auto. auto. intros. apply IsValid_inc. apply IHn. Qed.


 Fixpoint reqMember (r : RequestItem) (ls : RequestLS) : bool :=
 match ls with
 | emptyRequestLS => false
 | ConsRequestLS x x0 => if (eq_dec_RequestItem x r) then true else reqMember r x0
 end.
Print smallStep. 
 Definition get_desc (r :RequestItem) : Description :=
  match r with
   | requestItem d x => d
    end.
(*
Theorem goSmall :  forall n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  bigStep (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol ( n) AReceive pp2 rls2 un2 ls2) 
  = Some (Stop, Stop) -> exists p, smallStepn p ((getProtocol (n) ASend pp1 rls1 un1 ls1), (getProtocol ( n) AReceive pp2 rls2 un2 ls2)) = ((Stop,Stop),0).
  Proof. intros. induction n. simpl in H. exists 1. simpl. refl.
    subst.   proto.      *)