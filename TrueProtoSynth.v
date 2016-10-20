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

(*Add LoadPath "/users/paulkline/Documents/coqs/dependent-crypto".
Add LoadPath "/users/paulkline/Documents/coqs/cpdt/src".
Add LoadPath "C:\Users\Paul\Documents\coqs\dependent-crypto".
Add LoadPath "C:\Users\Paul\Documents\coqs\cpdt\src". *)
Require Import MyShortHand.

(*This defines what the type of measuring these things should be. *)

Definition measurementDenote (d: Description) :=
match d with
 | descriptor r => (match r with
    | pcrMR n => nat
    | virusCheckerNameR => nat
    | virusCheckerVersionR => bool
    end)
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
   | constValue (d: Description) : (measurementDenote d) -> Const 
   | constRequest : Description -> Const
   | constStop : Const.
   
Inductive Term :=
 | variable : VarID -> Term
 | const : Const -> Term
 .
Inductive Condition :=
 | IsMyTurntoSend : Condition
 | QueuedRequestsExist : Condition
 | ExistsNextDesire : Condition
 | CanSend :  Condition
 | IsSend :  Condition
 | IsMeasurement : Term -> Condition
 | IsRequest : Term -> Condition
 | IsStop : Term -> Condition
.


Inductive Computation := 
 | compGetMessageToSend
 | compGetNextRequest
 . 
 Inductive Effect :=
 | effect_HandleRequest : Term -> Effect
 | effect_ReduceStatewithMeasurement : Term -> Effect
 | effect_MvFirstDesire :  Effect
 .  
 Inductive Participant :=
 |  ATTESTER
 |  APPRAISER. 
 Theorem eq_dec_Participant : forall x y : Participant, {x = y} + {x <> y}.
 Proof. decide equality. Defined.
 
Inductive Statement :=
 | SendStatement : Term -> Participant -> Participant -> Statement
 | ReceiveStatement : VarID -> Statement
 | EffectStatement : Effect -> Statement
 | Compute : VarID -> Computation -> Statement
 | Assignment : VarID -> Term -> Statement
 | Choose : Condition -> Statement -> Statement -> Statement
 | Chain : Statement -> Statement -> Statement
 | StopStatement : Statement
 | EndStatement : Statement
 | Skip : Statement
 | Wait : Statement
.




Notation "'IFS' x 'THEN' y 'ELSE' z" := (Choose x y z)(at level 80, right associativity). 
Notation "x '>>' y" := (Chain x y)  (at level 60, right associativity).
(*Notation "(x >> .. >> y)" := (Chain x .. (Chain y StopMessage) ..).*)

Definition VarState := list (VarID*Const).
Inductive ProState :=
 (*  action <who am I?> privacyPol <things I want to ask for!> <Things I've asked for and am waiting for a response> tosend *)
 | proState : Action -> Participant ->  PrivacyPolicy -> RequestLS -> RequestLS -> list Description
      -> ProState.
Inductive State :=
 state : VarState -> ProState -> State.       

Fixpoint varSubst' (t : Term) (ls : VarState) : option Const :=
match t with
 | variable vid => match ls with
                     | nil => None
                     | cons pr ls' => if (eq_dec_VarID (fst pr) vid) then 
                           Some (snd pr)
                          else 
                           varSubst' t ls'
                   end
 | const x => Some ( x)
end.
 
Definition varSubst (t : Term) (st : State ) : option Const :=
match st with
 | state varst _ => varSubst' t varst
end.


    
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

(* the option indicates that a condition failed to be met *)
Definition reduceStateWithMeasurement (v : Const) (st : State) : option State := 
 match v with
 | constRequest _ => Some st
 | constStop => Some st
 | constValue d denotedVal => (match st with
                                | state varst  prost=> (match prost with
                                    | proState a p pp toReq myUnresolved tosend => 
                                       (match (reduceUnresolved d denotedVal myUnresolved) with
                                         | Some newUnresolvedState => Some ( 
                                            state varst 
                                              (proState a p (reducePrivacy d denotedVal pp) toReq     
                                                        newUnresolvedState tosend))
                                         | None => None
                                       end)
                                    end)
                              end)
 end.  

(* Answered the question: "Can I comply with this request? "
 
 We need the Priv Pol back because in has been modified. we remove the 
 requested item from the privacy policy. This is a quick and dirty way 
 of ensuring measurement deadlock never occurs because subsequent 
 requests for the item will be denied (because no privacy policy found for item) 
 
 The const in the middle is the message we should send back which can be:
  1. The requested measurement-- you approve (constValue _ _)
  2. absolutely not! (aka, constStop)
  3. Or perhaps I will give this measurment away if you give me something I want first. 
 
 This leads us into the third argument we receive back. Perhaps this isn't the best way of 
 defining this, but the third argument is the requirement that must be met by the measurment
 in the third case from above. ie, "I need to see some credentials." what exactly must be met.
 
*)

Fixpoint findandMeasureItem (pp : PrivacyPolicy) (d : Description) : option (Const*RequestItem) :=
match pp with
 | EmptyPolicy => None
 | @ConsPolicy dp rule_d pp' => if (eq_dec_Description dp d) then 
     match rule_d with
       | @rule _ your reqrment => Some (constRequest your, requestItem your reqrment)
       | free _ => Some (constValue d (measure d), requestItem d (freeRequirement d) )
       | never _ => Some ( constStop, requestItem d (neverRequirement d)) (*don't matter *)
       | multiReqAnd _ rule1 morerules => Some ( constStop, requestItem d (neverRequirement d)) (* TODO *)
       | multiReqOr _ rule1 morerules => Some (constStop, requestItem d (neverRequirement d)) (* TODO *)
      end
    else findandMeasureItem pp' d 
end.
Fixpoint rmAllFromPolicy (pp : PrivacyPolicy) (d : Description) : PrivacyPolicy :=
match pp with
 | EmptyPolicy => EmptyPolicy
 | @ConsPolicy dp r pp' => if (eq_dec_Description dp d) then rmAllFromPolicy pp' d
      else
      @ConsPolicy dp r (rmAllFromPolicy pp' d)
end. 
Fixpoint handleRequest' (pp : PrivacyPolicy) (d : Description) :=
 (match findandMeasureItem pp d with 
   | None => (rmAllFromPolicy pp d,constStop, requestItem d (neverRequirement d))
   | Some (mvalue,reqItem) => (rmAllFromPolicy pp d, mvalue, reqItem)
  end). 
  
Lemma removedFromPrivacyHelper : forall pp d, exists c ri, 
 handleRequest' pp d = (rmAllFromPolicy pp d,c,ri).
 Proof. intros. induction pp. simpl. eauto.
 simpl. destruct (eq_dec_Description d0 d).
 destruct r. eexists. eexists.  eauto.
 eexists. eexists.     
  eauto.
  eexists. eexists. eauto.
  eexists. eexists. eauto.
  eexists. eexists. eauto.
  
  destruct (findandMeasureItem pp d). destruct p. eexists. eexists. eauto.
  eexists. eexists. reflexivity.
  Qed.
  Hint Resolve removedFromPrivacyHelper. 
Lemma removedFromPrivacyHelper2 : forall pp d pp' c ri, 
 handleRequest' pp d = (pp',c,ri) -> 
 pp' = (rmAllFromPolicy pp d).
 Proof.  intros.
 destruct pp. simpl.
 inversion H. auto.
 simpl.
 simpl in H.
 simpl. destruct (eq_dec_Description d0 d). destruct r.
 subst. inversion H; subst. reflexivity.
 subst. inversion H; subst. reflexivity.
 subst. inversion H; subst. reflexivity.
 subst. inversion H; subst. reflexivity.
 subst. inversion H; subst. reflexivity.
 destruct findandMeasureItem . destruct p.
 subst. inversion H; subst. reflexivity.
 subst. inversion H; subst. reflexivity.
 Qed.
 Hint Resolve removedFromPrivacyHelper2. 

Theorem youCantFindit : forall pp d, findandMeasureItem (rmAllFromPolicy pp d) d = None.
Proof. intros. induction pp. auto.
simpl. destruct (eq_dec_Description d0 d). assumption.
simpl. destruct (eq_dec_Description d0 d). contradiction.
assumption.
Qed. 

Hint Resolve youCantFindit. 


Theorem removedFromPrivacy : forall pp d pp' c ri,
 handleRequest' pp d = (pp',c,ri) -> 
 findandMeasureItem pp' d = None.
 Proof. intros. assert (pp' = rmAllFromPolicy pp d). eauto.
  rewrite H0. eauto.
 Qed.
Hint Resolve removedFromPrivacy. 
(*
Fixpoint handleRequest' (pp : PrivacyPolicy) (d : Description) : 
(PrivacyPolicy * Const * RequestItem):=
 match pp with
 | EmptyPolicy => (EmptyPolicy, constStop, requestItem d (neverRequirement d))  (*by default, do not give away*)
 | @ConsPolicy dp rule_d pp' => if (eq_dec_Description dp d) 
    then
      match rule_d with
       | @rule _ your reqrment => (pp', constRequest your, requestItem your reqrment)
       | free _ => (pp', constValue d (measure d), requestItem d (freeRequirement d) )
       | never _ => (pp', constStop, requestItem d (neverRequirement d)) (*don't matter *)
       | multiReqAnd _ rule1 morerules => (pp', constStop, requestItem d (neverRequirement d)) (* TODO *)
       | multiReqOr _ rule1 morerules => (pp', constStop, requestItem d (neverRequirement d)) (* TODO *)
      end
    else
     match handleRequest' pp' d with
       | (ppres,messres,reqRes) => (@ConsPolicy dp rule_d ppres,messres,reqRes)
     end
 end. 
 *)
Definition handleRequestST (st: State) (d: Description) := match st with
 | state vars prostate => match prostate with
     | proState a p pp b unres dls => match(handleRequest' pp d) with 
                                | (pp',c,ri) => state ((toSendMESSAGE,c)::vars) (proState a p pp' b (ConsRequestLS ri unres) dls)
                                                  
                              end
end
end. 

 (* ls is the list of DESCRIPTIONS requested from me. This function is used when it is
 your turn to send something, and tells whether or not you can send the measurement of the request. You may not be able to because you have nothing left to request. (nil). 
 Your privacy policy allows for you to send the requested measurement.
  Possible reasons for failure:
 1.   The request is an unsatifiable object from the privacy policy. 
 *)
Definition canSendST (st : State) : option Description :=
match st with
 | state vars prostate => match prostate with
                           | proState _ _ pp _ _ ls =>  canSend ls pp
                          end
end.


Definition assign (var : VarID) (val : Const) (st : State) :=
  match st with
 | state varls prostate => state ((var,val)::varls) prostate
end. 

Definition isMyTurn (st : State) : bool :=
match st with
 | state vs ps => (match ps with
     | proState a _ _ _ _ _ => (match a with
                                 | ASend => true
                                 | AReceive => false
                                end)
     end)
end.
Definition queuedRequestsExist (st : State) := 
match st with
 | state vs ps => match ps with
       | proState _ _ _ _ _  nil => false
       | proState _ _ _ _ _  _ => true
        end

 end. 
Definition existsNextDesire (st : State) :=
match st with
 | state _ ps =>match ps with
            | proState _ _ _ wants _ _ =>match wants with
                             | emptyRequestLS => false
                             | ConsRequestLS x x0 => true
                            end
            end
end.

Fixpoint evalChoose (cond : Condition) (st: State) : bool :=
 (match st with
 | state varst prostate => (match prostate with
      | proState act p pp toReq unres ls => (match cond with
               | IsMyTurntoSend => isMyTurn st
               | QueuedRequestsExist => queuedRequestsExist st
               | ExistsNextDesire => existsNextDesire st
               | CanSend => (match (canSend ls pp) with 
                     | None => false
                     | Some _ => true
                     end)
               | IsSend => (match act with
                   | ASend => true
                   | AReceive => false
                   end)

               | IsMeasurement term => (match (varSubst term st) with
                    | None => false
                    | Some (constValue _ _) => true
                    | _ => false
                    end)
               | IsRequest term => (match (varSubst term st) with
                    | None => false
                    | Some (constRequest _) => true
                    | _ => false
                    end)
               | IsStop term => (match (varSubst term st) with
                    | None => false
                    | Some constStop => true
                    | _ => false
                    end)
               end) 
      end)

end)
.

Fixpoint receiveMess (n : Network) (p : Participant) : option Const :=
match n with 
 | nil => None
 | cons m ls => match m with 
                | networkMessage from to c => match eq_dec_Participant p to with 
                    | left _ => Some c
                    | right _ =>  receiveMess ls p
                    end 
                end
end.

Fixpoint rmMess (n : Network) (p : Participant) : Network :=
 match n with 
 | nil => nil
 | cons m ls => match m with 
                | networkMessage from to c => match eq_dec_Participant p to with 
                    | left _ =>  ls
                    | right _ =>  m :: (rmMess ls p)
                    end 
                end
end.
 
Fixpoint receiveN (n : Network) (p : Participant) : option (Const*Network) :=
match (receiveMess n p) with 
 | None => None
 | Some c => Some (c,rmMess n p)
end. 


Require Import Omega. 
Theorem receivingShrinks' : forall c n p, receiveMess n p = Some c -> 
length n = length (rmMess n p) + 1.
Proof. intros.
induction n. inversion H.
simpl in H.
destruct a.
simpl. simpl in H.
destruct (eq_dec_Participant p p1). subst. inversion H; subst. omega.
   simpl.  rewrite IHn. auto. auto.
Qed. 
Hint Resolve receivingShrinks'.


(*

Theorem receivingShrinks : forall n c p n', receiveN n p = Some (c,n') -> 
length n = length n' + 1.
Proof. intros. induction n. simpl. inversion H.
simpl. intro. intro. intro.     destruct a.  destruct (eq_dec_Participant p p1).
intros. 
 inversion H. subst. omega.
destruct (receiveMess n p).
intros. inversion H; subst.   
 intros. inversion H; subst.
simpl. omega.     
   auto.         
unfold receiveN. simpl.  
  intros  s. destruct n. simpl in H. inversion H.
unfold receiveN in H. destruct p. simpl in H.   
    induction n. intros. simpl in H. inversion H.
intros.
erewrite <- IHn. 
    simpl. 
auto. omega.        
*)

Definition fst3 {A B C : Type} (tripl : (A * B * C)) : A := match tripl with 
  (a,_,_) => a
  end.
Fixpoint stmHead (stm : Statement) : Statement :=
 match stm with 
  | (Chain stm1 _) => stmHead stm1
  | x => x
 end.  
   (*
Inductive isError : Statement -> Prop :=
 | isvarsubsterr : isError VariableSubstError
 | isMeasurmentReqNotMet : isError MeasurementRequirementNotMet
 | isVarAssErr : isError VariableAssignmentError
 .
Hint Constructors isError. *)
Print  reduceUnresolved. 




Definition getMe (st: State) : Participant :=
 match st with
 | state _ prostate => match prostate with
                        | proState _ p _ _ _ _ => p
end

end.

Definition mvNextDesire (st : State) : State :=
match st with
 | state vars ps =>match ps with
            | proState a b c wants e f =>(match wants with
                   | emptyRequestLS => state vars (proState a b c 
                      emptyRequestLS e f)
                   | ConsRequestLS ri rest => state vars (proState a b c rest
                      (ConsRequestLS ri e) f )
                  end) 
            end
end.


Definition handleEffect (e : Effect) (st : State) : option State :=
match e with
 | effect_HandleRequest t => match (varSubst t st) with 
                              | Some (constRequest d) => Some (handleRequestST st d)
                              | _ => None
                              end 
 | effect_ReduceStatewithMeasurement t => match (varSubst t st) with 
                                           | Some c => (reduceStateWithMeasurement c st)
                                           | _ => None
                                           end
 | effect_MvFirstDesire => Some (mvNextDesire st)
end.
Check measure. 
Definition getNextDesire (st : State) : option Description :=
match st with
 | state _ ps =>match ps with
            | proState _ _ _ wants _ _ =>(match wants with
                             | emptyRequestLS => None
                             | ConsRequestLS ri _ => (match ri with
                                         | requestItem d x => Some d
                                        end)

                            end)
            end
end.


Definition handleCompute (comp : Computation) (st : State) : option Const :=
 match comp with
  | compGetMessageToSend => match (canSendST st) with 
                              | Some d => Some (constValue d (measure d))
                              | None => None
                            end
  | compGetNextRequest =>  (match (getNextDesire st) with 
                              | None => None
                              | Some desire => Some (constRequest desire)
                            end)
 end
.
 
(*Inductive Statement :=
 | SendStatement : Term -> Participant -> Participant -> Statement (*for now/simplicity, Participant not a variable*)
 | ReceiveStatement : VarID -> Statement
 | EffectStatement : Effect -> Statement
(* | ReduceStatewithMeasurement : Term -> Statement*)
 | Compute : VarID -> Computation -> Statement
 | Assignment : VarID -> Term -> Statement
 | Choose : Condition -> Statement -> Statement -> Statement
 | Chain : Statement -> Statement -> Statement
 | StopStatement : Statement
 | Skip : Statement
 | Wait : Statement
 | VariableSubstError
 | MeasurementRequirementNotMet
 | VariableAssignmentError
 | Done
.
*)

 Reserved Notation " x '⇓'  x'"
                  (at level 40).

Inductive stmEval : (Statement * State * Network) -> (Statement * State * Network) -> Prop :=
   | E_Send : forall st n term f t v, (varSubst term st) = Some v -> 
              v <> constStop ->  
              (SendStatement term f t, st, n) ⇓
                (Skip, st, (sendOnNetwork f t v n))
   | E_SendStop : forall st n term f t v, (varSubst term st) = Some constStop ->  (SendStatement term f t, st, n) ⇓
      (StopStatement, st, (sendOnNetwork f t v n))
   | E_ReceiveStop : forall st n n' vid,
        receiveN n (getMe st) = Some (constStop,n')  ->
        (ReceiveStatement vid, st,n) ⇓ (StopStatement, assign vid constStop st, n')
   | E_ReceiveWait : forall st n vid,
        receiveN n (getMe st) = None -> 
        (ReceiveStatement vid, st, n) ⇓ (Wait >> (ReceiveStatement vid) ,st ,n)
   | E_Wait : forall st n happy,
        receiveN n (getMe st) = Some happy ->
        (Wait, st, n) ⇓ (Skip, st, n)
   | E_Receive : forall st n n' vid mess,
        receiveN n (getMe st) = Some (mess,n')  ->
        mess <> constStop ->
        (ReceiveStatement vid, st,n) ⇓ (Skip, assign vid mess st, n')
   | E_Effect : forall st n effect st',
        handleEffect effect st = Some st' ->  
        (EffectStatement effect, st, n) ⇓ (Skip, st',n)
   | E_Compute : forall st n vid compTerm c, 
        handleCompute compTerm st = Some c -> 
        (Compute vid compTerm, st, n) ⇓
        (Skip, assign vid c st, n)
   | E_Assign : forall st n vid term2 c, 
       (varSubst term2 st) = Some c -> 
       (Assignment vid term2, st, n) ⇓ (Skip, assign vid c st, n)
   | E_ChooseTrue : forall st n cond stmTrue stmFalse,
      (evalChoose cond st) = true -> 
      (Choose cond stmTrue stmFalse, st, n) ⇓ (stmTrue, st, n)
   | E_ChooseFalse : forall st n cond stmTrue stmFalse,
      (evalChoose cond st) = false -> 
      (Choose cond stmTrue stmFalse, st, n) ⇓ (stmFalse, st, n)
   | E_Chain : forall st n st' n' stm1 stm2, 
       (stm1,st,n) ⇓ (Skip,st',n') -> 
       (Chain stm1 stm2, st, n) ⇓ (stm2,st',n')
   | E_ChainBad : forall st n st' n' stm1 stm2, 
       (stm1,st,n) ⇓ (StopStatement,st',n') -> 
       (Chain stm1 stm2, st, n) ⇓ (StopStatement,st',n')
   | E_ChainWait : forall st n st' n' stm1 stm2, 
       (stm1,st,n) ⇓ (Wait >> stm1,st',n') -> 
       (Chain stm1 stm2, st, n) ⇓ (Wait >> stm1 >> stm2,st',n')
   | E_Skip : forall st n, (Skip, st, n)  ⇓ (Skip, st, n )
   
   | E_End : forall st n, 
       (EndStatement, st, n) ⇓ (EndStatement, st, n) 
   | E_Stop : forall st n, 
       (StopStatement, st, n) ⇓ (StopStatement, st, n) 
   | E_KeepWaiting : forall st n stm, 
       receiveN n (getMe st) = None -> 
       (Wait >> stm, st, n) ⇓ (Wait >> stm, st, n) 
   | E_KeepWaiting2 : forall st n, 
       receiveN n (getMe st) = None -> 
       (Wait, st, n) ⇓ (Wait, st, n) 
   where "x '⇓' x' " := (stmEval x x').
Hint Constructors stmEval. 

Inductive BigStep_stmEval : (Statement * State * Network) -> (Statement * State * Network) -> Prop := 
| bigstep_stm_simpl : forall stm st n stm' st' n', stmEval (stm,st,n) (stm',st',n') -> BigStep_stmEval (stm,st,n) (stm',st',n')
| bigstep_stm_step :  forall stm st n stm' st' n' stm'' st'' n'', 
BigStep_stmEval (stm,st,n) (stm',st',n') -> 
BigStep_stmEval (stm',st',n') (stm'',st'',n'') -> 
BigStep_stmEval (stm,st,n) (stm'',st'',n'').

Notation "x ⇓⇓ x'" := (BigStep_stmEval x x') (at level 35).
 
Hint Constructors BigStep_stmEval. 


Definition notMe (p : Participant) : Participant :=
match p with
 | ATTESTER => APPRAISER
 | APPRAISER => ATTESTER
end.
Definition proto_handleCanSend (st : State) :=
 IFS CanSend
    THEN Compute toSendMESSAGE compGetMessageToSend >>
         SendStatement (variable toSendMESSAGE) (getMe st) (notMe (getMe st)) >> 
         EndStatement
    ELSE (*Can't send and queued request exists *) 
      SendStatement (const constStop) (getMe st) (notMe (getMe st)) >> 
      StopStatement (*Give up!*).
 
Definition proto_handleExistsNextDesire (st : State) :=
Compute toSendMESSAGE compGetNextRequest >>
EffectStatement effect_MvFirstDesire >> 
SendStatement (variable toSendMESSAGE) (getMe st) (notMe (getMe st)) >> 
EndStatement.

Definition proto_handleNoNextDesire (st : State) :=
SendStatement (const constStop) (getMe st) (notMe (getMe st)) >> 
StopStatement. 

Definition proto_handleCantSend (st : State):= IFS ExistsNextDesire
    THEN 
      proto_handleExistsNextDesire st
    ELSE (* I must send, nothin queued, nothin left I want, quit! *)
      proto_handleNoNextDesire st
      . 
 
Definition proto_handleIsMyTurnToSend (st: State) := 
(
IFS QueuedRequestsExist
  THEN 
   proto_handleCanSend st
  ELSE (*No queued up things for me. So I can continue down my list of things I want. *)
   proto_handleCantSend st
).

 
Definition proto_handleNotMyTurnToSend (st : State) :=
ReceiveStatement (receivedMESSAGE) >>
IFS (IsMeasurement (variable (receivedMESSAGE)))
 THEN 
   EffectStatement (effect_ReduceStatewithMeasurement (variable (receivedMESSAGE)) ) >> EndStatement
 ELSE
  (IFS (IsRequest (variable (receivedMESSAGE)))
    THEN 
      EffectStatement (effect_HandleRequest (variable (receivedMESSAGE))) >> EndStatement
    ELSE (*we must have received a stop *)
      StopStatement
  ). 


Definition OneProtocolStep (st : State) : Statement :=
  (* first step is to find out if we're sending or receiving. *)
    (IFS IsMyTurntoSend 
     THEN
      proto_handleIsMyTurnToSend st
      
    ELSE (* I AM RECEIVING *) 
     proto_handleNotMyTurnToSend st
     ).
       
Definition getProState (st : State) : ProState :=
match st with
 | state _ ps => ps
end. 

Fixpoint headStatement (stm : Statement) : Statement :=
match stm with
 | Chain stm1 _ => headStatement stm1 
 | stmm => stmm
end. 

Theorem onlyEffect_effects : forall (stm stm': Statement) (st st': State) (n n' : Network),
 (stm,st,n) ⇓ (stm',st',n') ->  
 getProState st = getProState st' \/ exists e, (headStatement stm) = EffectStatement e. 
Proof.
intro. induction stm ; try (intros; inversion H; left; reflexivity).
intros. simpl. left. inversion H. subst. destruct st.  auto. auto.
destruct st; auto.
intros. right. exists e. auto.
intros. left. inversion H; subst.   destruct st. auto.
intros. left. destruct st; inversion H; subst. auto.
simpl. 
intros. inversion H; subst.    eapply IHstm1.
eauto.

eapply IHstm1. eauto.

eapply IHstm1. eauto.

eapply IHstm1. constructor.  eauto.
Qed.

Theorem onlySendOrReceiveChangesNetwork : forall (stm stm': Statement) (st st': State) (n n' : Network),
 (stm,st,n) ⇓ (stm',st',n') -> 
 n = n' \/
 (exists t p1 p2, headStatement stm = SendStatement t p1 p2) \/
 (exists vid, headStatement stm = ReceiveStatement vid)
 .
 Proof. intro. induction stm; intros; try (right; left; exists t; exists p; exists p0; reflexivity) ||
 (try (left; inversion H; subst; reflexivity)).
 inversion H; subst.
   
 right. right. exists v. auto.
 left. reflexivity.
 right. right. exists v. auto.
 inversion H; subst.
 eauto.
 eauto.
 eauto.
 eauto.
 Qed.
 
Theorem canSendST_implies_handleExists : forall st, evalChoose CanSend st = true -> exists c, handleCompute compGetMessageToSend st = Some c.
Proof.
intros; simpl in H;  simpl; destruct st; simpl; destruct p; destruct (canSend l p0);  eauto;
inversion H. Qed.
Hint Resolve canSendST_implies_handleExists.

Fixpoint mostRecentFromMe (st : State) (n : Network) : bool :=
match n with
 | nil => false
 | cons m nil => match m with
    | networkMessage f _ _ => if (eq_dec_Participant f (getMe st)) then true else false
    end
 | cons _ ls => mostRecentFromMe st ls
end. 
 
Tactic Notation "inv" hyp(H) := inversion H; subst.
 
 Theorem evalSendTurn : forall  st n, (evalChoose IsMyTurntoSend st) = true -> (OneProtocolStep st ,st,n) ⇓ (proto_handleIsMyTurnToSend st, st, n).
Proof.
intros; unfold OneProtocolStep; constructor; assumption.
Qed.
Hint Resolve evalSendTurn. 

Theorem evalReceiveTurn : forall st n, (evalChoose IsMyTurntoSend st) = false -> (OneProtocolStep st ,st,n) ⇓ (proto_handleNotMyTurnToSend st, st, n).
Proof. intros; unfold OneProtocolStep; constructor; assumption.
Qed.
Hint Resolve evalReceiveTurn.

Theorem eval_myTurnToSend_queuedRequest : forall st n, (evalChoose QueuedRequestsExist st) = true -> (proto_handleIsMyTurnToSend st, st, n) ⇓ 
(proto_handleCanSend st, st, n).
Proof. intros; unfold proto_handleIsMyTurnToSend; constructor; assumption.
Qed.
Hint Resolve eval_myTurnToSend_queuedRequest.
Theorem eval_myTurnToSend_NOqueuedRequest : forall st n, (evalChoose QueuedRequestsExist st) = false -> (proto_handleIsMyTurnToSend st, st, n) ⇓ 
(proto_handleCantSend st, st, n).
Proof. intros; unfold proto_handleIsMyTurnToSend; constructor; assumption.
Qed.
Hint Resolve eval_myTurnToSend_NOqueuedRequest.      


Theorem eval_existsNextDesire : forall st n, (evalChoose ExistsNextDesire st) = true -> (proto_handleCantSend st, st, n) ⇓ 
 (proto_handleExistsNextDesire st, st, n)
.
Proof. intros; unfold proto_handleIsMyTurnToSend; constructor; assumption.
Qed.
Hint Resolve eval_existsNextDesire.      

Print OneProtocolStep. 

Theorem eval_NoNextDesire : forall st n, (evalChoose ExistsNextDesire st) = false -> (proto_handleCantSend st, st, n) ⇓ 
 (proto_handleNoNextDesire st, st, n)
.
Proof. intros; unfold proto_handleIsMyTurnToSend; constructor; assumption.
Qed.
Hint Resolve eval_NoNextDesire.

Theorem sendTurnHelper : forall st, isMyTurn st = true -> evalChoose IsMyTurntoSend st = true.
Proof.
intros. destruct st. destruct p. auto. Qed.
Hint Resolve sendTurnHelper.

Theorem varSubstConst : forall st c, varSubst (const c) st = Some c.
Proof. intros. destruct st. destruct v. auto. auto.
Qed.
Hint Resolve varSubstConst.

Hint Unfold OneProtocolStep.
Hint Unfold proto_handleCanSend.
Hint Unfold proto_handleCantSend.
Hint Unfold proto_handleNoNextDesire.
Hint Unfold proto_handleIsMyTurnToSend.
Hint Unfold proto_handleNotMyTurnToSend.
Hint Unfold proto_handleExistsNextDesire.  

Tactic Notation "cca" := repeat constructor; assumption. 

(*(EndStatement, assign toSendMESSAGE x (state v p), sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) x n)
⇓⇓ (EndStatement, st', n')
*)
Theorem eval1 : forall v p n, evalChoose IsMyTurntoSend (state v p) = true -> 
evalChoose QueuedRequestsExist (state v p)                          = true ->
evalChoose CanSend (state v p)                                      = true -> exists c,  
 (OneProtocolStep (state v p), (state v p), n) ⇓⇓ (EndStatement, assign toSendMESSAGE c (state v p) ,sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) c n).
Proof. intros. unfold OneProtocolStep.
assert (evalChoose CanSend (state v p) = true). assumption.  
apply canSendST_implies_handleExists in H1. destruct H1.
exists x. 
eapply bigstep_stm_step. cca.
unfold proto_handleIsMyTurnToSend.
eapply bigstep_stm_step. cca.
unfold proto_handleCanSend. 
eapply bigstep_stm_step. constructor. constructor.   cca.
eapply bigstep_stm_step. constructor. constructor. constructor.
rewrite H1. auto.

eapply bigstep_stm_step. constructor. constructor. constructor. simpl.  auto.       cca.
Qed.

(*(StopStatement, state v p, sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) constStop n) ⇓⇓ (EndStatement, ?st, ?n')*)
Theorem eval2 : forall v p n, 
evalChoose IsMyTurntoSend (state v p)      = true -> 
evalChoose QueuedRequestsExist (state v p) = true ->
evalChoose CanSend (state v p)             = false ->   
(OneProtocolStep (state v p), (state v p), n) ⇓⇓ (StopStatement, state v p , (sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) constStop n)).
Proof. intros. unfold OneProtocolStep.
eapply bigstep_stm_step. cca.
unfold proto_handleIsMyTurnToSend.
eapply bigstep_stm_step. cca.
unfold proto_handleCanSend.
eapply bigstep_stm_step. constructor. apply E_ChooseFalse. assumption.
eapply bigstep_stm_step. constructor. constructor. constructor. auto.
constructor. 
cca.
Qed.

    Theorem ifwillthenway : forall st, evalChoose ExistsNextDesire st = true ->exists c,  handleCompute compGetNextRequest st = Some c .
    Proof.
    intros. destruct st. destruct p. destruct r.   simpl. exists constStop. intros. inversion H.
    simpl. destruct r. exists (constRequest d). auto. 
    Qed.


(*(EndStatement, mvNextDesire (assign toSendMESSAGE x (state v p)), sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) x n)
*)
Theorem eval3 : forall v p n, 
evalChoose IsMyTurntoSend (state v p)      = true -> 
evalChoose QueuedRequestsExist (state v p) = false ->
evalChoose ExistsNextDesire (state v p)    = true ->   exists r,
(OneProtocolStep (state v p), (state v p), n) ⇓⇓ (EndStatement, mvNextDesire (assign toSendMESSAGE r (state v p)), (sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) r n)).
Proof. intros. unfold OneProtocolStep.

assert (evalChoose ExistsNextDesire (state v p) = true). assumption.  

apply ifwillthenway in H1. destruct H1. exists x. 
eapply bigstep_stm_step. cca.
unfold proto_handleIsMyTurnToSend.
eapply bigstep_stm_step. cca.
unfold proto_handleCantSend. 
eapply bigstep_stm_step. cca.
eapply bigstep_stm_step. constructor. constructor. constructor. rewrite H1. auto. 


eapply bigstep_stm_step. cca.
eapply bigstep_stm_step; constructor; constructor; constructor; destruct p; destruct r;    simpl; eauto.
Qed.

(*
(StopStatement, state v p, sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) constStop n)*)
Theorem eval4 : forall v p n, 
evalChoose IsMyTurntoSend (state v p)      = true -> 
evalChoose QueuedRequestsExist (state v p) = false ->
evalChoose ExistsNextDesire (state v p)    = false -> 
(OneProtocolStep (state v p), (state v p), n) ⇓⇓ (StopStatement, state v p, (sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) constStop n)).
Proof. intros. unfold OneProtocolStep.
eapply bigstep_stm_step.  cca.
eapply bigstep_stm_step. cca.
eapply bigstep_stm_step. cca.
eapply bigstep_stm_step. constructor. autounfold. constructor. constructor. auto.
auto. 
Qed.

Theorem eval5 : forall v p n d c, 
evalChoose IsMyTurntoSend (state v p)      = false -> 
receiveN n (getMe (state v p)) = Some (constValue d c, tail n) -> exists pp',
reduceStateWithMeasurement (constValue d c) (assign receivedMESSAGE (constValue d c) (state v p)) = Some pp' -> 
(OneProtocolStep (state v p), (state v p), n) ⇓⇓ (EndStatement, (assign receivedMESSAGE (constValue d c) (state v p)), tail n).
Proof. intros. unfold OneProtocolStep.
eexists. intros. 
eapply bigstep_stm_step. cca.
eapply bigstep_stm_step. autounfold. constructor. constructor. Print E_Receive.  constructor.  apply H0.  unfold not. intros. inv H2.
eapply bigstep_stm_step. constructor. constructor. simpl. destruct p. auto.
eapply bigstep_stm_step.    constructor. constructor. constructor. unfold handleEffect. rewrite <- H1.  reflexivity. auto.
Qed.

Theorem eval6 : forall v p n r, 
evalChoose IsMyTurntoSend (state v p)      = false -> 
receiveN n (getMe (state v p)) = Some (constRequest r, tail n) -> 
(OneProtocolStep (state v p), (state v p), n) ⇓⇓ (EndStatement, (handleRequestST (assign receivedMESSAGE (constRequest r) (state v p)) r), tail n).
Proof. intros. unfold OneProtocolStep.
 intros. 
eapply bigstep_stm_step. cca.
eapply bigstep_stm_step. autounfold. constructor. constructor. Print E_Receive.  constructor.  apply H0.  unfold not. intros. inv H1.
eapply bigstep_stm_step. constructor. apply E_ChooseFalse. simpl. destruct p. auto.
eapply bigstep_stm_step.    constructor. constructor. simpl. destruct p. auto.
eapply bigstep_stm_step. cca. auto.   
Qed.

Theorem eval7 : forall v p n, 
evalChoose IsMyTurntoSend (state v p)      = false -> 
receiveN n (getMe (state v p)) = Some (constStop, tail n) -> 
(OneProtocolStep (state v p), (state v p), n) ⇓⇓ (StopStatement,  (assign receivedMESSAGE constStop (state v p)), tail n).
Proof. intros. unfold OneProtocolStep. 
 intros. 
eapply bigstep_stm_step. cca.
eapply bigstep_stm_step. autounfold. constructor. eapply E_ChainBad. constructor. apply H0. auto.
Qed.

Theorem eval8 : forall v p n, 
evalChoose IsMyTurntoSend (state v p)      = false -> 
receiveN n (getMe (state v p)) = None -> 
(OneProtocolStep (state v p), (state v p), n) ⇓⇓ (Wait >> (proto_handleNotMyTurnToSend (state v p)),   (state v p), n).
Proof. intros. unfold OneProtocolStep. 
 intros. 
eapply bigstep_stm_step. constructor. apply E_ChooseFalse. auto.
eapply bigstep_stm_step. autounfold. constructor. eapply E_ChainWait.  eapply E_ReceiveWait. assumption.
constructor. apply E_KeepWaiting. assumption.
Qed.
  
Hint Resolve eval1 eval2 eval3 eval4 eval5 eval6 eval7 eval8.  

Theorem sendOnNetworkAppends : forall  f t c n, length (sendOnNetwork f t c n) = length n + 1.
Proof. intros. induction n.
auto.
simpl. auto.
Qed.
Hint Resolve sendOnNetworkAppends.         
Require Import Omega. 

Theorem receiveWhenStop : forall n vid v p n',
receiveN n (getMe (state v p)) = Some (constStop, n') ->
(ReceiveStatement vid, (state v p), n) ⇓ 
(StopStatement,assign vid constStop (state v p), n').
Proof. intros.  eapply E_ReceiveStop. assumption.
Qed.
Theorem oneStepProtoStopsWhenTold :forall v p n n', evalChoose IsMyTurntoSend (state v p) = false -> 
receiveN n (getMe (state v p)) = Some (constStop, n') -> 
((OneProtocolStep (state v p) , (state v p), n) ⇓⇓ (StopStatement, assign receivedMESSAGE constStop (state v p), n')) .
Proof. intros.
eapply bigstep_stm_step. constructor. apply E_ChooseFalse. auto.
constructor. constructor. apply receiveWhenStop. auto.
Qed.

Definition getPrivacy (st : State) : PrivacyPolicy :=
match st with
 | state _ ps => match ps with
    | proState _ _ pp _ _ _ => pp
end
end.
SearchAbout PrivacyPolicy.


Theorem isRemovedFromPrivacyhandleST : forall st d, 
findandMeasureItem (getPrivacy (handleRequestST st d)) d = None.
Proof. intros. destruct st. simpl. destruct p.
destruct p0. simpl. auto.
simpl.    
destruct (eq_dec_Description d0 d). destruct r1; simpl; auto.

destruct (findandMeasureItem p0 d). destruct p1. simpl.
destruct r1;
destruct (eq_dec_Description d0 d); contradiction || auto.

simpl. 
destruct r1;
destruct (eq_dec_Description d0 d); contradiction || auto.
Qed.
Hint Resolve isRemovedFromPrivacyhandleST.

Theorem isRemovedFromPrivacy : forall st st' n t d, 
  varSubst t st = Some (constRequest d) -> 
  (EffectStatement (effect_HandleRequest t), st, n) ⇓ (Skip, st',n) -> 
  findandMeasureItem (getPrivacy st') d = None.
Proof. intros. inversion H0. subst.
simpl in H2. rewrite H in H2. inversion H2.
auto.
Qed.  


     
Theorem sendWillSend : forall v p n,evalChoose IsMyTurntoSend (state v p) = true -> exists  st' n', 
((OneProtocolStep (state v p) , (state v p), n) ⇓⇓(EndStatement, st', n') 
\/  
(OneProtocolStep (state v p) , (state v p), n) ⇓⇓ (StopStatement, st', n') 
)
 /\  length n + 1 = length n' .
Proof.
intros. 
destruct (evalChoose QueuedRequestsExist (state v p)) eqn: quedRes.
destruct (evalChoose CanSend (state v p)) eqn : cansend. 

Check eval1.

specialize eval1 with (v:=v) (p := p) (n := n).
intro.
apply H0 in H.
destruct H.
eexists. eexists.
split.
left.  
eapply H.
auto.
auto.
auto.

eexists. eexists.
auto.

Check eval3. 
destruct (evalChoose ExistsNextDesire (state v p)) eqn: existsmydesire.
specialize eval3 with (v:=v) (p := p) (n := n).
intro.
apply H0 in H.
destruct H.
eexists. eexists. 
split. left.
apply H.
auto.
auto.
auto.

Check eval4. 
eexists. eexists.
 
auto.
Qed.
Fixpoint lastMessage (n:Network) : option NetworkMessage :=
match n with
 | nil => None
 | cons x nil => Some x
 | cons _ xs => lastMessage xs
end.




Fixpoint hasNetworkAction (stm:Statement) : bool :=
match stm with
 | SendStatement x x0 x1 => false
 | ReceiveStatement x => false
 | _ => true
end.
Fixpoint countMaxNetworkActions (stm : Statement) : nat :=
match stm with
 | SendStatement x x0 x1 => 1
 | ReceiveStatement x => 1
 | Choose x x0 x1 => max (countMaxNetworkActions x0) (countMaxNetworkActions x1)
 | Chain x x0 => (countMaxNetworkActions x) + (countMaxNetworkActions x0)
 | _ => 0
end. 

Fixpoint countMinNetworkActions (stm : Statement) : nat :=
match stm with
 | SendStatement x x0 x1 => 1
 | ReceiveStatement x => 1
 | Choose x x0 x1 => min (countMinNetworkActions x0) (countMinNetworkActions x1)
 | Chain x x0 => (countMinNetworkActions x) + (countMinNetworkActions x0)
 | _ => 0
end.

Theorem onestepProtocolmaxAction_eq_minAction : forall st, 
countMinNetworkActions (OneProtocolStep st) = (countMaxNetworkActions (OneProtocolStep st)).
Proof. intros; compute; reflexivity.
Qed.

Theorem onestepProtocolmaxAction_eq_1 : forall st, 
(countMaxNetworkActions (OneProtocolStep st)) = 1.
Proof. intros. compute. reflexivity. 
Qed.

Fixpoint countMinSends (stm : Statement) : nat :=
match stm with
 | SendStatement x x0 x1 => 1
 | Choose x x0 x1 => min (countMinSends x0) (countMinSends x1)
 | Chain x x0 => (countMinSends x) + (countMinSends x0)
 | _ => 0
end. 

Fixpoint countMinReceives (stm : Statement) : nat :=
match stm with
 | ReceiveStatement x => 1
 | Choose x x0 x1 => min (countMinReceives x0) (countMinReceives x1)
 | Chain x x0 => (countMinReceives x) + (countMinReceives x0)
 | _ => 0
end.

Fixpoint countMaxSends (stm : Statement) : nat :=
match stm with
 | SendStatement x x0 x1 => 1
 | Choose x x0 x1 => max (countMaxSends x0) (countMaxSends x1)
 | Chain x x0 => (countMaxSends x) + (countMaxSends x0)
 | _ => 0
end. 

Fixpoint countMaxReceives (stm : Statement) : nat :=
match stm with
 | ReceiveStatement x => 1
 | Choose x x0 x1 => max (countMaxReceives x0) (countMaxReceives x1)
 | Chain x x0 => (countMaxReceives x) + (countMaxReceives x0)
 | _ => 0
end.

Inductive SingularNetworkAction :Statement -> Action -> Prop :=
 | s_Send (stm : Statement): (countMaxReceives stm) = 0 /\ 
                             (countMinSends stm) = 1 /\
                             (countMaxSends stm) = 1 -> SingularNetworkAction stm ASend
 | s_Receive (stm : Statement): (countMaxSends stm) = 0 /\
                             (countMinReceives stm) = 1 /\ 
                             (countMaxReceives stm) = 1 -> SingularNetworkAction stm AReceive.
Hint Constructors SingularNetworkAction. 
Inductive NetworkActionChain : Action -> Prop :=
 | nac_emptySend : NetworkActionChain ASend
 | nac_emptyReceive : NetworkActionChain AReceive
 | nac_Send {stm} : SingularNetworkAction stm ASend -> NetworkActionChain AReceive -> NetworkActionChain ASend
 | nac_Receive {stm}: SingularNetworkAction stm AReceive -> NetworkActionChain ASend -> NetworkActionChain AReceive.
 Hint Constructors NetworkActionChain. 

Theorem oneStepSend : forall st stm' n, 
 evalChoose IsMyTurntoSend st = true -> 
 (OneProtocolStep st, st, n) ⇓ (stm', st, n) ->
 SingularNetworkAction stm' ASend.
 Proof. intros. inversion H0; subst.
 apply s_Send. simpl. omega. rewrite H in H2. inversion H2.
 Qed.

Theorem oneStepReceives : forall st stm' n, 
 evalChoose IsMyTurntoSend st = false -> 
 (OneProtocolStep st, st, n) ⇓ (stm', st, n) ->
 SingularNetworkAction stm' AReceive.
 Proof. intros. inversion H0; subst.
 rewrite H in H2. inversion H2.
 apply s_Receive.  simpl. omega.
 Qed.
 Hint Resolve oneStepSend oneStepReceives. 
 SearchAbout Action.
 
 Definition reverse (a : Action) : Action := 
 match a with
 | ASend => AReceive
 | AReceive => ASend
end. 

 Definition switchSendRec ( st : State) : State := 
  match st with
   | state vars ps=> match ps with
       | proState a b c d e f => state vars (proState (reverse a) b c d e f)
      end

  end. 
  Definition getAction ( st : State) : Action := 
  match st with
   | state vars ps=> match ps with
       | proState a b c d e f => a
      end
  end. 

 Inductive DualEval : (Statement*State) ->(Statement* State) -> Network -> Prop :=
 
  | dulift : forall leftState rightState, 
       (getAction leftState) = reverse (getAction rightState) -> 
        DualEval (OneProtocolStep leftState, leftState) (OneProtocolStep rightState, rightState) nil
  | duLeft : forall leftSTM leftState rightSTM rightState n,
      DualEval (leftSTM, leftState) (rightSTM,rightState) n -> 
      forall leftState' n',
      (leftSTM , leftState, n) ⇓⇓ (EndStatement, leftState', n') -> 
      DualEval (OneProtocolStep (switchSendRec leftState'), switchSendRec leftState') (rightSTM, rightState) n'
       
  | duRight : forall leftSTM leftState rightSTM rightState n,
      DualEval (leftSTM,leftState) (rightSTM, rightState) n -> 
      forall rightState' n',
      (rightSTM , rightState, n) ⇓⇓ (EndStatement, rightState', n') -> 
      DualEval (leftSTM, leftState) (OneProtocolStep (switchSendRec rightState'), switchSendRec rightState') n'
      
  | leftIsWait : forall leftSTM leftState rightSTM rightState n,
      DualEval (leftSTM, leftState) (rightSTM,rightState) n -> 
      forall leftState' n' stm',
      (leftSTM , leftState, n) ⇓⇓ (Wait >> stm', leftState', n') -> 
      forall n'' rightState',
      (rightSTM , rightState, n') ⇓⇓ (EndStatement, rightState', n'') ->
      DualEval (Wait >> stm', leftState') (OneProtocolStep (switchSendRec rightState'), (switchSendRec rightState')) n''
      
  | rightIsWait : forall leftSTM leftState rightSTM rightState n,
      DualEval (leftSTM, leftState) (rightSTM,rightState) n -> 
      forall rightState' n' stm',
      (rightSTM , rightState, n) ⇓⇓ (Wait >> stm', rightState', n') -> 
      forall n'' leftState',
      (leftSTM , leftState, n') ⇓⇓ (EndStatement, leftState', n'') ->
      DualEval (OneProtocolStep (switchSendRec leftState'), (switchSendRec leftState')) (Wait >> stm', rightState') n'' 
  | duFinishLeftFirst : forall stmL stL stL' stmR stR stR' n n' n'',
      (stmL , stL, n) ⇓⇓ (StopStatement, stL', n') ->
      (stmR, stR, n')  ⇓⇓ (StopStatement, stR', n'') -> 
      DualEval (stmL, stL) (stmR, stR) n -> 
      DualEval (StopStatement,stL') (StopStatement,stR') n''
  | duFinishRightFirst : forall stmL stL stL' stmR stR stR' n n' n'',
      (stmR, stR, n)  ⇓⇓ (StopStatement, stR', n') -> 
      (stmL , stL, n') ⇓⇓ (StopStatement, stL', n'') ->
      DualEval (stmL, stL) (stmR, stR) n -> 
      DualEval (StopStatement,stL') (StopStatement,stR') n''.
      Hint Constructors DualEval.
Theorem finalHelper : forall stL stR n, reverse (getAction stL) = getAction stR -> 
DualEval (OneProtocolStep stL, stL) (OneProtocolStep stR, stR) n -> exists stL stR n, 
DualEval (StopStatement,stL) (StopStatement, stR) n.
Proof. intros. destruct stL, stR. destruct p, p0. destruct a, a0; simpl in H.
inversion H. simpl in H0.     simpl in H.       destruct stL.    
Theorem final : exists stL stR n, 
DualEval (StopStatement,stL) (StopStatement, stR) n.
Proof. intros.   eexists. eexists. eexists.
econstructor.   
 