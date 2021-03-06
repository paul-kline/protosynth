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
Add LoadPath "/home/paul/Documents/coqs/protosynth/cpdt/src" as Cpdt.
Require Export MyShortHand.

(*Require Import String.*) 
(*
Require Import Coq.Relations.Relation_Definitions.
*)
(*Add LoadPath "/users/paulkline/Documents/coqs/dependent-crypto".

Add LoadPath "C:\Users\Paul\Documents\coqs\dependent-crypto".
Add LoadPath "C:\Users\Paul\Documents\coqs\cpdt\src". *)
Add LoadPath "C:\Users\Paul\Documents\coqStuff\protosynth".
Add LoadPath "/nfs/users/paulkline/Documents/coqs/protosynth/cpdt/src" .
Require Export ProtoSynthDataTypes.
 
(* Require Export ProtoSynthDataTypeEqualities.
 *)
Require Export ProtoSynthProtocolDataTypes. 
Require Export Coq.Lists.List.
Add LoadPath "/home/paul/Documents/coqs/protosynth/cpdt/src" as Cpdt. 
Require Export Cpdt.CpdtTactics.
(*
Require Import Coq.Program.Equality.
Require Import Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Peano_dec.
*)






(*Examples *)
Definition  des1 := (descriptor (pcrMR 1)). 
Eval compute in (measurementDenote des1).
Definition req1 : (Requirement des1 ).

apply requirement. simpl. exact ((fun (x : nat) => Nat.leb x 7)).
Defined.
Definition req2 := 
 requirement (des1) ((fun (x : nat) => Nat.leb x 7)).

Definition myRule1 := rule (des1) (requirement (descriptor (pcrMR 2))
 (fun x : nat => Nat.leb x 9)).
Check myRule1.
Check ConsPolicy.
Print myRule1. 
Definition myPrivacyPolicy := ConsPolicy myRule1 EmptyPolicy.


Definition myrequirement1 := fun (x : nat) => (x > 7).


(* This helps with protocol generation. *)



 
 
 
 (* placeholder measurement function. need this to exist *) 
 Definition measure (d: Description) : measurementDenote d.
 Proof. destruct d. destruct d. simpl. exact n.
 simpl. exact 0.
 simpl. exact 1. 
 Defined.
 

 


 
 (* Now we get into functions needed to define the getProtocol function. 
    Due to coqs linear nature, we must define in this order, but know that
    it's existence was only deamed necessary during the construction of getProtocol. 
    
    In short, the purpose of this function is to reduce the size of the list of the 
    things we are waiting on measurements for. The option type is used to indicate
    if the requirement posed upon the value v has failed to be met.
    *)
Fixpoint reduceUnresolved (d : Description) (v : measurementDenote d)
(unresolved : RequestLS) : option RequestLS. refine match unresolved with
 | emptyRequestLS => Some emptyRequestLS
 | ConsRequestLS r x0 => match r with
      | requestItem dr reqment => if eq_dec_Description dr d then
          match reqment with
            | requirement _ f => match f _ with
               | true => Some x0 (*Do I need recursive call here? Is it possible to be in here twice? *)
               | false => None (*Requirement not met. give up on everything *)
              end
          end
        else (*if eq_dec_Description is false..*)
          match reduceUnresolved d v x0 with 
            | Some some => Some (ConsRequestLS r some)
            | None => None
          end
     end
 end. rewrite <- e in v. exact v. Defined. 
 

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


(* Now that we know some measurement value, can we ease any requirements stated in the privacy policy? 
Stay tuned to find out! *)
Fixpoint reduceRule {theird myd: Description} (v : (measurementDenote theird)) (myRule : Rule myd) : (Rule myd). refine (
match myRule with
       | @rule _ your reqrment => if (eq_dec_Description theird your) then
          (match reqrment with
            | requirement _ f => if (f _) then (free myd)
                               else  (never myd)
          end)
          else (* leave it alone! this isn't it.*) myRule
      (* | multiReqAnd _ rule1 rule2 => multiReqAnd myd (_) (_)
       | multiReqOr _ rule1 rule2 =>  multiReqOr myd (_) (_) *)
       | _ => myRule
       
end). subst. exact v.
(* for mutli and/or *)
(*
 exact (reduceRule theird myd v rule1). exact (reduceRule theird myd v rule2).
 exact (reduceRule theird myd v rule1). exact (reduceRule theird myd v rule2).
*)
Defined.


(**
reducePrivacy is now just repeated application of reduceRule to all terms in the policy.*)
Fixpoint reducePrivacy (d : Description) (v : (measurementDenote d)) (priv : PrivacyPolicy) : PrivacyPolicy :=
match priv with
 | EmptyPolicy => EmptyPolicy
 | @ConsPolicy dp rule_d pp' => @ConsPolicy dp (reduceRule v rule_d) (reducePrivacy d v pp')
 end.

(**
We indicate the variable was not in the state by the None option.*)
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

(** 
This is a much handier version that deconstructs the state for you.
*)
Definition varSubst (t : Term) (st : State ) : option Const :=
match st with
 | state varst _ => varSubst' t varst
end.



(** 
When we send a message, it gets appended to the end of the list. This makes receiving
in the correct order easier. *)
Fixpoint sendOnNetwork (from : Participant) (to : Participant) (m : Const) (n : Network) : Network :=
 match n with
 | nil => cons (networkMessage from to m) nil
 | cons n1 nls => cons n1 (sendOnNetwork from to m nls) 
end. 

(**
Who are you expecting a message from? Who am I? and the network.
This function finds the first message in the list that is from the expected party to me.*)
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

(**
This is a handy check to see if the network is empty or not. Syntactic sugar. Tasty*)
Definition net_isEmpty ( n : Network) : bool :=
 match n with
 | nil => true
 | cons x x0 => false
end.

(** This function gives us a new state to replace the passed in state. We are also
given a Const value, which must be the result of a measurment. The state is modified
in the following ways:
1. reduceUnresolved is called with the given value. Recall that reduceUnresolved will optinally
give a reduced list of unresolved RequestItems. If it gives us back none, we know some outstanding requirement
has not been met. Therefore notice that here we propagate this information by including a No as the AllGood
signal.  
2. Whether or not we successfully have reducedUnresolved, we call reducePrivacy as well. Recall that this function
softens the heart of the privacy policy, loosening up any restrictions tied to that value.
OR: it hardens its heart. making the requirement 'never' if the value fails the requirement. It is evaluated here 

Calling reducePrivacy when reduceUnresolved gives back 'none' seems supurfluous, and indeed it is but aids in proving.
*)
Definition reduceStateWithMeasurement (v : Const) (st : State) : State := 
 match v with
 | constValue d denotedVal => (match st with
                                | state varst  prost=> (match prost with
                                    | proState a g p pp toReq myUnresolved tosend => 
                                       (match (reduceUnresolved d denotedVal myUnresolved) with
                                         | Some newUnresolvedState => ( 
                                            state varst 
                                              (proState a Yes p (reducePrivacy d denotedVal pp) toReq     
                                                        newUnresolvedState tosend))
                                         | None => state varst (proState a No p (reducePrivacy d denotedVal pp) toReq
                                                       myUnresolved tosend)
                                       end)
                                    end)
                              end)
 | _ => st
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
(** 
Actually...
This function answers the question of how to respond to a mesurement request.
We iterate through our privacy policy, if there is no rule for the Description, we indicate
this by returning 'none'. This is meant to be isomorphic to the response when pattern matching 
on a 'never' rule for a particular Description, but for some reason, I return a None. I'm not sure why.
Let's continue.
If we find a rule for this measurement request (Description), if it has a remaining rule that has not
been simplified down to 'free' or 'never' (in otherwords, we haven't already received the value as a result
of some other action), we return a request for the item we wish to know about to release the initially desired
measurement and the requirement its value must meet along with it. If we find a 'free' rule attached to the 
desired measurment value, we perform the measuring, and return no restriction (free) because it  feels right to do so. It is not used as all when a value is returned as the first in the pair. The reason why we return this supurfluous value in these cases is it simplifies the case we return with a counter request.
In the case we encounter a 'never' rule, we return a constStop. 
*)
Fixpoint findandMeasureItem (pp : PrivacyPolicy) (d : Description) : option (Const*RequestItem) :=
match pp with
 | EmptyPolicy => None
 | @ConsPolicy dp rule_d pp' => if (eq_dec_Description dp d) then 
     match rule_d with
       | @rule _ your reqrment => Some (constRequest your, requestItem your reqrment)
       | free _ => Some (constValue d (measure d), requestItem d (freeRequirement d) )
       | never _ => Some ( constStop, requestItem d (neverRequirement d)) (*don't matter *)
       (*| multiReqAnd _ rule1 morerules => Some ( constStop, requestItem d (neverRequirement d)) (* TODO *)
       | multiReqOr _ rule1 morerules => Some (constStop, requestItem d (neverRequirement d)) (* TODO *)
      *)
      end
    else findandMeasureItem pp' d 
end.

(**
If findandMeasureItem returns a constValue, it is, in fact, the result of the initial request (d=d0). 
*)
Theorem thm_findAndMeasureItemL : forall pp d d0 val x, findandMeasureItem pp d = Some (constValue d0 val, x) -> d = d0.
Proof. intros. induction pp.  inv H.
destruct r. simpl in H. destruct (eq_dec_Description d1 d). subst. inv H.
apply IHpp. assumption.
simpl in H. destruct (eq_dec_Description d1 d). subst. inv H. subst. refl.
apply IHpp. assumption.
simpl in H. destruct (eq_dec_Description d1 d). subst. inv H. apply IHpp. assumption.
(* mutlAnd or case *)
(*
simpl in H.  destruct (eq_dec_Description d1 d). subst. inv H. apply IHpp. assumption.
simpl in H.  destruct (eq_dec_Description d1 d). subst. inv H. apply IHpp. assumption.
*)
Qed.
Hint Resolve thm_findAndMeasureItemL.
 
(** 
This function removes all instances of a description from a privacyPolicy.
Remember, we only want to allow someone to request something once. Therefore, this 
function will be called on each description we receive as a request. In hindsight,
PrivacyPolicy should be implemented as a Set.  
*) 
Fixpoint rmAllFromPolicy (pp : PrivacyPolicy) (d : Description) : PrivacyPolicy :=
match pp with
 | EmptyPolicy => EmptyPolicy
 | @ConsPolicy dp r pp' => if (eq_dec_Description dp d) then rmAllFromPolicy pp' d
      else
      @ConsPolicy dp r (rmAllFromPolicy pp' d)
end.

(**
If findandMeasureItem returns None, we still removeAll occurances in the policy.
Recall None means the item didn't exist in our privacy policy. We still call rmAllFromPolicy
because it doesn't hurt anything, and aids in the proving. We of course stop in this case
and throw on a never requirment because its fitting (though completely unnecessary).
If we get back a some, we propagate the results. 
The purpose of this function is to call findandMeasureItem and removeAll from the 
privacy policy.
*)  
Fixpoint handleRequest' (pp : PrivacyPolicy) (d : Description) :=
 (match findandMeasureItem pp d with 
   | None => (rmAllFromPolicy pp d,constStop, requestItem d (neverRequirement d))
   | Some (mvalue,reqItem) => (rmAllFromPolicy pp d, mvalue, reqItem)
  end).
Check handleRequest'.  
Lemma thm_handleRequestL : forall pp d pp' d2 v z, handleRequest' pp d = (pp',constValue d2 v,z) -> d = d2.
Proof. intros. destruct pp.  simpl in H. inversion H. sh. 
destruct (eq_dec_Description d0 d) eqn:hh. destruct r. 
inversion H.  inversion H. auto. inversion H.
destruct (findandMeasureItem pp d) eqn:hhh. destruct p. 
inversion H. subst. 
eapply thm_findAndMeasureItemL. eauto.
inversion H. 
Qed. 
Hint Resolve thm_handleRequestL. 

Definition snd3 {A B C : Type} (x : (A*B*C) ): B := match x with 
 | (_,b,_) => b
 end.
 
(**
In all calls to handleRequest', the privacy policy has the requested item removed.
*) 
Lemma thm_removedFromPrivacyHelper : forall pp d, exists c ri, 
 handleRequest' pp d = (rmAllFromPolicy pp d,c,ri).
 Proof. intros. induction pp. simpl. eauto.
 simpl. destruct (eq_dec_Description d0 d).
 destruct r. eexists. eexists.  eauto.
 eexists. eexists.     
  eauto.
  eexists. eexists. eauto.
  (* multiand or cases *) 
  (*
  eexists. eexists. eauto.
  eexists. eexists. eauto.
  *)
  destruct (findandMeasureItem pp d). destruct p. eexists. eexists. eauto.
  eexists. eexists. reflexivity.
  Qed.
Hint Resolve thm_removedFromPrivacyHelper.
(*
Lemma handleReqSameD : forall pp d d0  val x y,  (handleRequest' pp d) = (x, constValue d0 val,y) -> d0 = d.
Proof. intros. destruct pp; intros.  simpl in H. inv H.
destruct r. simpl in H. destruct (eq_dec_Description d1 d). inv H.
destruct (findandMeasureItem pp d) eqn:eff. symmetry. destruct p. destruct c.  eapply findAndMeasureItemL. apply eff.   in eff.  
destruct pp, d. simpl in H. inv H. simpl in H.     (findandMeasureItem pp d). destruct p. apply IHpp.  inv H. subst.        
apply IHpp. 
simpl in H. destruct (eq_dec_Description d d0). subst. destruct r. inv H.
simpl in H. inv H. refl.
inv H. inv H. inv H.

apply IHpp. rewrite <- H. destruct pp. simpl. refl. simpl. refl.       
          
destruct r. 
simpl in H. destruct (eq_dec_Description d1 d). inv H.  subst. inv H. apply IHpp. assumption.        
  \/
snd3 (handleRequest' pp d) = constStop  .
Proof. intros. induction pp.  simpl. right. refl.
simpl.  
destruct (eq_dec_Description d0 d). destruct r. subst.
simpl. left.          

  Hint Resolve removedFromPrivacyHelper. 
  
  *)
  
Lemma thm_removedFromPrivacyHelper2 : forall pp d pp' c ri, 
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
 (* multi and or cases *)
 (*
 subst. inversion H; subst. reflexivity.
 subst. inversion H; subst. reflexivity.*)
 destruct findandMeasureItem . destruct p.
 subst. inversion H; subst. reflexivity.
 subst. inversion H; subst. reflexivity.
 Qed.
 Hint Resolve thm_removedFromPrivacyHelper2. 

(** If an item has been removed, findAndMeasureItemL will never succeed.*)
Theorem thm_youCantFindit : forall pp d, findandMeasureItem (rmAllFromPolicy pp d) d = None.
Proof. intros. induction pp. auto.
simpl. destruct (eq_dec_Description d0 d). assumption.
simpl. destruct (eq_dec_Description d0 d). contradiction.
assumption.
Qed. 

Hint Resolve thm_youCantFindit. 

(** After handling a request, subsequest requests of that description will fail.*)
Theorem thm_removedFromPrivacy : forall pp d pp' c ri,
 handleRequest' pp d = (pp',c,ri) -> 
 findandMeasureItem pp' d = None.
 Proof. intros. assert (pp' = rmAllFromPolicy pp d). eauto.
  rewrite H0. eauto.
 Qed.
Hint Resolve thm_removedFromPrivacy. 
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
 
(**
 The main purpose of this function is to 
  1. open up the state
  2. call handleRequest'
  3. give us a new state with: 
         a. the toSendMESSAGE variable set to the result of calling handleRequest'.
         b. appended the new requirment to our unresolved state.
         c. the reduced privacy policy
   
 *)
Definition handleRequestST (st: State) (d: Description) := match st with
 | state vars prostate => match prostate with
     | proState a g p pp b unres dls => match(handleRequest' pp d) with 
                                | (pp',c,ri) => state ((toSendMESSAGE,c)::vars) (proState a g p pp' b (ConsRequestLS ri unres) dls)
                                                  
                              end
end
end. 

 (* ls is the list of DESCRIPTIONS requested from me. 
   This function checks the head of the list to see if measuring the value
   will succeed or not. In other words, privacy policy allows it FOR FREE. no 
   counter request is needed. Otherwise constRequest would be in the middle. NOT
   constValue. 
 *)
 Definition canSend (ls : list Description) (priv : PrivacyPolicy) : option Description :=
(match ls with
 | nil => None
 | cons d ds => 
   (match (handleRequest' priv d) with 
     | (_, constValue d _,_) => Some d  
     | _ => None
     end)
end).
 
(**
This Theorem ensures that we are, in fact, returning the head of the 
request list, if we canSend.
*)
Theorem thm_canSendL : forall pp ls d, (canSend ls pp = Some d )-> (head ls) =Some  d.
Proof. intros. destruct ls. inv H. simpl in H.
simpl.
destruct (handleRequest' pp d0) eqn:hh.  destruct p. destruct c.
inv H.
 assert (d0 = d). eapply thm_handleRequestL.
eauto. subst. auto.  inv H. inv H. 
Qed. 
Hint Resolve thm_canSendL.

(** Simply sugar for call canSend. This one extracts the important bits from the state *)
Definition canSendST (st : State) : option Description :=
match st with
 | state vars prostate => match prostate with
                           | proState _ _ _ pp _ _ ls =>  canSend ls pp
                          end
end.

(**
Sugar for assigning a value to a variable in a state.*)
Definition assign (var : VarID) (val : Const) (st : State) :=
  match st with
 | state varls prostate => state ((var,val)::varls) prostate
end. 

(**
Simply checks if it is my turn to send or not. *)
Definition isMyTurn (st : State) : bool :=
match st with
 | state vs ps => (match ps with
     | proState a _ _ _ _ _ _ => (match a with
                                 | ASend => true
                                 | AReceive => false
                                end)
     end)
end.

(* Theorem isMyTurnTrue : forall st, isMyTurn st = true <-> gee
 *)

(**
Simply checks to see if a queued up request exists.
In other words, is someone waiting for something from me?
*)
Definition queuedRequestsExist (st : State) := 
match st with
 | state vs ps => match ps with
       | proState _ _ _ _ _ _  nil => false
       | proState _ _ _ _ _ _ _ => true
        end
 end.

(**
Simply checks if a next desire exists. Checks if there ar more requests
I would like to make of the other party.
*)
Definition existsNextDesire (st : State) :=
match st with
 | state _ ps =>match ps with
            | proState _ _ _ _ wants _ _ =>match wants with
                             | emptyRequestLS => false
                             | ConsRequestLS x x0 => true
                            end
            end
end.

(**
This is a biggie. This function determines how to handle evaluation of a condition into bool or false.
*)
Fixpoint evalChoose (cond : Condition) (st: State) : bool :=
 (match st with
 | state varst prostate => (match prostate with
      | proState act g p pp toReq unres ls => (match cond with
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
               | IsAllGood => (match st with
                             | state vars ps => (match ps with
                               | proState x g x1 x2 x3 x4 x5 => 
                                  (match g with
                                   | Yes => true 
                                   | No => false
                                   | Unset => false
                                    end)
                              end)
                            end)
               end) 
      end)

end)
.

(* receive from any? Do I want this?*)
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

(** Removes the message from the networ, IF one exists. *)
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
Fixpoint existsMessageForMe (n : Network) (p : Participant) : Prop :=
 match n with 
 | nil => False
 | cons m ls => match m with 
                | networkMessage from to c => match eq_dec_Participant p to with 
                    | left _ =>  True
                    | right _ =>  (existsMessageForMe ls p)
                    end 
                end
end.
Require Import Omega. 
Lemma thm_rmMessSmallerL : forall n p, existsMessageForMe n p  -> S (length  (rmMess n p))= length n. 
Proof. intros. induction n. simpl in H.  tauto.   
simpl.  destruct a. destruct (eq_dec_Participant p p1) eqn:hh. auto. 
simpl.  
simpl in H. rewrite hh in H. rewrite IHn.  auto. auto.
Qed.
Hint Resolve thm_rmMessSmallerL. 

(** Receive, getting a message for me if there is one, None otherwise. 
Upon successful receive, remove the message from the network.
*)
Fixpoint receiveN (n : Network) (p : Participant) : option (Const*Network) :=
match (receiveMess n p) with 
 | None => None
 | Some c => Some (c,rmMess n p)
end. 

Require Import Omega. 
Theorem thm_receivingShrinks' : forall c n p, receiveMess n p = Some c -> 
length n = length (rmMess n p) + 1.
Proof. intros.
induction n. inversion H.
simpl in H.
destruct a.
simpl. simpl in H.
destruct (eq_dec_Participant p p1). subst. inversion H; subst. omega.
   simpl.  rewrite IHn. auto. auto.
Qed. 
Hint Resolve thm_receivingShrinks'.

Lemma thm_receiveN_receiveMess : forall c n p, 
 receiveN n p = Some (c,rmMess n p) <-> receiveMess n p = Some c.
Proof. intros. split; intros.   induction n; intros. inv H.
simpl.  destruct a. destruct (eq_dec_Participant p p1) eqn:hh. 
simpl in H. rewrite hh in H.  inv H.  auto.
simpl in H.  rewrite hh in H. destruct (receiveMess n p).  inv H.  auto. 
inv H. 
(* other way. *)
induction n.  inv H. 
simpl. simpl in H.  destruct a. destruct (eq_dec_Participant p p1) eqn:hh. 
inv H.  auto.
simpl in H. destruct (receiveMess n p).  inv H.  auto. 
inv H.
Qed. 
Hint Resolve thm_receiveN_receiveMess.

Theorem thm_receiveN_NewNetworkrmMessage : forall c n n' p, receiveN n p = Some (c, n') -> n' = rmMess n p.
Proof. intros.  destruct n.  simpl in H. inv H. simpl in H.
destruct n.  destruct (eq_dec_Participant p p1) eqn:hh.  inv H.
simpl. rewrite hh.  auto. 
destruct (receiveMess n0 p).  inv H.  simpl. 
rewrite hh.  auto. inv H. 
Qed. 
Hint Resolve thm_receiveN_NewNetworkrmMessage.
Hint Rewrite thm_receiveN_NewNetworkrmMessage.     
Theorem thm_receivingShrinks : forall n c p n', receiveN n p = Some (c,n') -> 
length n = S (length n') .
Proof. intros.
intros. assert (receiveN n p = Some (c, n')). auto.   apply thm_receiveN_NewNetworkrmMessage in H. subst. 
induction n.  inv H0. simpl. assert (receiveN (a :: n) p = Some (c, rmMess (a :: n) p)).  auto. 
sh.  
destruct a. sh. destruct (eq_dec_Participant p p1) eqn:hh. auto. 
simpl.
rewrite IHn.  auto. 
destruct (receiveMess n p) eqn:hhh. apply thm_receiveN_receiveMess in hhh.
inv H0. 
auto. inv H0. 
Qed.

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
 | state _ (proState _ _ p _ _ _ _) =>  p
end.

(**
This function moves the next desired measurement into the unresolved
list.
*)
Definition mvNextDesire (st : State) : State :=
match st with
 | state vars (proState a g b c wants e f) =>(match wants with
                   | emptyRequestLS => state vars (proState a g b c 
                      emptyRequestLS e f)
                   | ConsRequestLS ri rest => state vars (proState a g b c rest
                      (ConsRequestLS ri e) f )
                  end) 
end.

(**
This function takes the desired measurement and stores it in the queue of things
I have been asked to measure.
*)
Definition storeRequest (d : Description) (st : State) : State :=
match st with
 | state vs ps => match ps with
      | proState x g x0 x1 x2 x3 queue => state vs (proState  x g x0 x1 x2 x3 (d :: queue))
end
end. 

(**
Removes from privacy given a state. Just a wrapper funtion. *)
Definition rm_f_Privacy_w_RequestST (d : Description) (st : State) : State :=
match st with
 | state vs (proState x g x0 pp x2 x3 x4) => 
   state vs (proState x g x0 (rmAllFromPolicy pp d) x2 x3 x4)
     
end.

(** Wrapper for removing the head of the queued up requests I have.
*)
Definition handleRmFstQueued (st : State) :=
match st with
 | state vs ps => match ps with
    | proState x g x0 x1 x2 x3 x4 => state vs
       (proState x g x0 x1 x2 x3 (tail x4)) 
end
end. 

(*
Fixpoint rmFromPP (pp : PrivacyPolicy) (d : Description) :=
match pp with
 | EmptyPolicy => EmptyPolicy
 | @ConsPolicy dp x x0 => if (eq_dec_Description d dp) then  rmFromPP x0 d 
                                                       else  @ConsPolicy dp x (rmFromPP x0 d)
end.
*) 

(**
Answers, what, if any is my counter request?
*)
Fixpoint getCounterReqItemFromPP (pp : PrivacyPolicy) (d : Description) : option RequestItem :=
match pp with
 | EmptyPolicy => None
 | @ConsPolicy dp x x0 => if (eq_dec_Description d dp) then match x with
   | @rule _ dd  r => Some (requestItem dd r)
   | free _ => None
   | never _ => None
 (*| multiReqAnd _ _ x0 => None
   | multiReqOr _ _ x0 => None*)
   end 
                          else      
                          (getCounterReqItemFromPP x0 d)
end. 

(** This function checks to see if a counter request is needed to release the
description asked of me. If there is none, this is reported by returning none.
If a counter is needed, the counter is added to the outstanding requests.
*)
Definition handlecp_ppUnresolved (d : Description)  (st : State) : option State := 
match st with
 | state vs (proState x g x0 pp x2 x3 x4) => match  getCounterReqItemFromPP pp d with 
                                      | None => None
                                      | Some reqI => Some (state vs (proState x g x0 pp x2 (ConsRequestLS reqI x3) x4))
                                      end

end. 

(**
Setter for allGood Property
*)
Definition setAllGood (g : AllGood) (st : State) : State:=
match st with
 | state var (proState x x0 x1 x2 x3 x4 x5) => state var (proState x g x1 x2 x3 x4 x5) 
end.
 
(* This is the mapping of state effects from the Effect Inductive type.
*)
Definition handleEffect (e : Effect) (st : State) : option State :=
match e with
 (*| effect_HandleRequest t => match (varSubst t st) with 
                              | Some (constRequest d) => Some (handleRequestST st d)
                              | _ => None
                              end *)
 | effect_StoreRequest t => match (varSubst t st) with 
                              | Some (constRequest r) => Some (storeRequest r st) 
                              | _ => None 
                              end
 | effect_ReducePrivacyWithRequest t=> match (varSubst t st) with 
                                        | Some (constRequest r) => Some (rm_f_Privacy_w_RequestST r st)
                                        | _ => None
                                        end
 | effect_ReduceStatewithMeasurement t => match (varSubst t st) with 
                                           | Some c =>Some (reduceStateWithMeasurement c st)
                                           | _ => None
                                           end
 | effect_MvFirstDesire => Some (mvNextDesire st)
 | effect_rmFstQueued  =>  Some (handleRmFstQueued st)
 | effect_cp_ppUnresolved t =>  match (varSubst t st) with 
                                           | Some (constRequest d) => (handlecp_ppUnresolved d st)
                                           | _ => None
                                           end
 | effect_setAllGood x  => Some (setAllGood x st)
end. 


Check measure.
(** Getter *) 
Definition getNextDesire (st : State) : option Description :=
match st with
 | state _ (proState _ _ _ _ wants _ _) =>
  (match wants with
     | emptyRequestLS => None
     | ConsRequestLS (requestItem d x) _ =>  Some d
   end)
          
end.

(** Getter for first unfulfilled description by me.*)
Definition getfstQueueAsConst (st : State) :=
match st with
 | state _ ps => match ps with
    | proState x g x0 x1 x2 x3 x4 => match x4 with
 | nil => None
 | cons x x0 => Some (constRequest x)
end
end
end.

(**
mapping from computations to actual actions. *)
Definition handleCompute (comp : Computation) (st : State) : option Const :=
 match comp with
  | compGetfstQueue => getfstQueueAsConst st
  | compGetMessageToSend => match (canSendST st) with 
                              | Some d => Some (constValue d (measure d))
                              | None => None
                            end
  | compGetNextRequest =>  (match (getNextDesire st) with 
                              | None => None
                              | Some desire => Some (constRequest desire)
                            end)
 end.

Reserved Notation " x '⇒'  x'"
                  (at level 40).
Inductive stmEval : (Statement * State * Network) -> (Statement * State * Network) -> Prop :=
   | E_Send : forall st n term f t v, (varSubst term st) = Some v -> 
              v <> constStop ->  
              (SendStatement term f t, st, n) ⇒
                (Skip, st, (sendOnNetwork f t v n))
   | E_SendStop : forall st n term f t v, (varSubst term st) = Some constStop ->  (SendStatement term f t, st, n) ⇒
      (StopStatement,  st, (sendOnNetwork f t v n))
   | E_ReceiveStop : forall st n n' vid,
        receiveN n (getMe st) = Some (constStop,n')  ->
        (ReceiveStatement vid, st,n) ⇒ (StopStatement, assign vid constStop st, n')
   | E_ReceiveWait : forall st n vid,
        receiveN n (getMe st) = None -> 
        (ReceiveStatement vid, st, n) ⇒ (Wait >> (ReceiveStatement vid) ,st ,n)
   | E_Wait : forall st n happy,
        receiveN n (getMe st) = Some happy ->
        (Wait, st, n) ⇒ (Skip, st, n)
   | E_Receive : forall st n n' vid mess,
        receiveN n (getMe st) = Some (mess,n')  ->
        mess <> constStop ->
        (ReceiveStatement vid, st,n) ⇒ (Skip, assign vid mess st, n')
   | E_Effect : forall st n effect st',
        handleEffect effect st = Some st' ->  
        (EffectStatement effect, st, n) ⇒ (Skip, st',n)
   | E_Compute : forall st n vid compTerm c, 
        handleCompute compTerm st = Some c -> 
        (Compute vid compTerm, st, n) ⇒
        (Skip, assign vid c st, n)
   | E_Assign : forall st n vid term2 c, 
       (varSubst term2 st) = Some c -> 
       (Assignment vid term2, st, n) ⇒ (Skip, assign vid c st, n)
   | E_ChooseTrue : forall st n cond stmTrue stmFalse,
      (evalChoose cond st) = true -> 
      (Choose cond stmTrue stmFalse, st, n) ⇒ (stmTrue, st, n)
   | E_ChooseFalse : forall st n cond stmTrue stmFalse,
      (evalChoose cond st) = false -> 
      (Choose cond stmTrue stmFalse, st, n) ⇒ (stmFalse, st, n)
   | E_Chain : forall st n st' n' stm1 stm2, 
       (stm1,st,n) ⇒ (Skip,st',n') -> 
       (Chain stm1 stm2, st, n) ⇒ (stm2,st',n')
   | E_ChainBad : forall st n st' n' stm1 stm2, 
       (stm1,st,n) ⇒ (StopStatement,st',n') -> 
       (Chain stm1 stm2, st, n) ⇒ (StopStatement,st',n')
   | E_ChainWait : forall st n st' n' stm1 stm2, 
       (stm1,st,n) ⇒ (Wait >> stm1,st',n') -> 
       (Chain stm1 stm2, st, n) ⇒ (Wait >> stm1 >> stm2,st',n')
   (*| E_Skip : forall st n, (Skip, st, n)  ⇒ (Skip, st, n )
   | E_SkipEnd : forall st n, (Skip, st, n) ⇒ (EndStatement, st, n )*)
   (*| E_End : forall st n, 
       (EndStatement, st, n) ⇒ (EndStatement, st, n)
   | E_Stop : forall st n, 
       (StopStatement, st, n) ⇒ (StopStatement, st, n)
     *)   
   | E_KeepWaiting : forall st n stm, 
       receiveN n (getMe st) = None -> 
       (Wait >> stm, st, n) ⇒ (Wait >> stm, st, n) 
   | E_KeepWaiting2 : forall st n, 
       receiveN n (getMe st) = None -> 
       (Wait, st, n) ⇒ (Wait, st, n) 
   where "x '⇒' x' " := (stmEval x x').
Hint Constructors stmEval. 
Ltac chain := (apply E_Chain) + (eapply E_Chain).

Reserved Notation "x ⇒* x'"(at level 35). 
Inductive MultiStep_stmEval : (Statement * State * Network) -> (Statement * State * Network) -> Prop := 
| multistep_id : forall stm st n stm' st' n', stmEval (stm,st,n) (stm',st',n') -> MultiStep_stmEval (stm,st,n) (stm',st',n')
| multistep_step : forall stm st n stm' st' n' stm'' st'' n'', 
(stm, st, n)    ⇒* (stm', st', n')  -> 
(stm',st',n')   ⇒* (stm'',st'',n'') -> 
(stm, st, n) ⇒* (stm'',st'',n'')
 where "x ⇒* x'" := (MultiStep_stmEval x x').
Hint Constructors MultiStep_stmEval.
Definition notMe (p : Participant) : Participant :=
match p with
 | ATTESTER => APPRAISER
 | APPRAISER => ATTESTER
end.

Lemma thm_endEval : forall st st' stm' n n', 
(EndStatement, st, n) ⇒* (stm', st', n') -> False.
Proof. intros. dependent induction H. inversion H. eauto.
Qed.
Hint Resolve thm_endEval.



Definition proto_handleCanSend (st : State) :=
 IFS CanSend
    THEN Compute toSendMESSAGE compGetMessageToSend >>
         SendStatement (variable toSendMESSAGE) (getMe st) (notMe (getMe st)) >> 
         Compute (variden 1) compGetfstQueue >>
         EffectStatement (effect_ReducePrivacyWithRequest (variable (variden 1))) >>
         EffectStatement effect_rmFstQueued >>
         EffectStatement (effect_setAllGood Yes) >> (*all good here! *)
         EndStatement
    ELSE (*Can't send and queued request exists *)
      EffectStatement (effect_setAllGood No) >> (* no, this is bad! *) 
      SendStatement (const constStop) (getMe st) (notMe (getMe st)) >> 
      StopStatement (*Give up!*).
 
Definition proto_handleExistsNextDesire (st : State) :=
Compute toSendMESSAGE compGetNextRequest >>
EffectStatement effect_MvFirstDesire >> 
SendStatement (variable toSendMESSAGE) (getMe st) (notMe (getMe st)) >> 
EffectStatement (effect_setAllGood Yes) >>
EndStatement.

Definition proto_handleNoNextDesire (st : State) :=
EffectStatement (effect_setAllGood Yes) >> (*all is well, just out! *)
SendStatement (const constStop) (getMe st) (notMe (getMe st)) >> 
StopStatement. 

Definition proto_handleCantSend (st : State):= IFS ExistsNextDesire
    THEN 
      proto_handleExistsNextDesire st
    ELSE (* I must send, nothin queued, nothin left I want, quit! *)
      proto_handleNoNextDesire st
      . 
 
Definition proto_handleIsMyTurnToSend (st: State) := 
(IFS IsAllGood THEN
    EffectStatement (effect_setAllGood Unset) >>
    IFS QueuedRequestsExist
      THEN 
         proto_handleCanSend st
      ELSE (*No queued up things for me. So I can continue down my list of things I want. *)
         proto_handleCantSend st
 ELSE
    SendStatement (const constStop) (getMe st) (notMe (getMe st)) >>
    StopStatement
).

Definition proto_handleNotMyTurnToSend (st : State) :=
ReceiveStatement (receivedMESSAGE) >>
IFS (IsMeasurement (variable (receivedMESSAGE)))
 THEN 
   EffectStatement (effect_ReduceStatewithMeasurement (variable (receivedMESSAGE)) ) >> EndStatement
 ELSE
  (IFS (IsRequest (variable (receivedMESSAGE)))
    THEN 
      EffectStatement (effect_StoreRequest (variable (receivedMESSAGE))) >> EndStatement
    ELSE (*we must have received a stop *)
      StopStatement
  ). 


Definition OneProtocolStep (st : State) : Statement :=
  (* first step is to find out if we're sending or receiving. *)
(
IFS IsMyTurntoSend THEN
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

Theorem thm_onestepProtocolmaxAction_eq_minAction : forall st, 
countMinNetworkActions (OneProtocolStep st) = (countMaxNetworkActions (OneProtocolStep st)).
Proof. intros; compute; reflexivity.
Qed.

Theorem thm_onestepProtocolmaxAction_eq_1 : forall st, 
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

Theorem thm_oneStepSend : forall st stm' n, 
 evalChoose IsMyTurntoSend st = true -> 
 (OneProtocolStep st, st, n) ⇒ (stm', st, n) ->
 SingularNetworkAction stm' ASend.
 Proof. intros. inversion H0; subst.
 apply s_Send. simpl. omega. rewrite H in H2. inversion H2.
 Qed.

Theorem thm_oneStepReceives : forall st stm' n, 
 evalChoose IsMyTurntoSend st = false -> 
 (OneProtocolStep st, st, n) ⇒ (stm', st, n) ->
 SingularNetworkAction stm' AReceive.
 Proof. intros. inversion H0; subst.
 rewrite H in H2. inversion H2.
 apply s_Receive.  simpl. omega.
 Qed.
 Hint Resolve thm_oneStepSend thm_oneStepReceives. 
 SearchAbout Action.
 
 Definition reverse (a : Action) : Action := 
 match a with
 | ASend => AReceive
 | AReceive => ASend
end. 

 Definition switchSendRec ( st : State) : State := 
  match st with
   | state vars ps=> match ps with
       | proState a g b c d e f => state vars (proState (reverse a) g b c d e f)
      end

  end. 
  Definition getAction ( st : State) : Action := 
  match st with
   | state vars ps=> match ps with
       | proState a g b c d e f => a
      end
  end. 
  (*⇒
  U+21af ⇊
  ↡ ⍗ *)
  Definition rever (st : State) : State := 
match st with
 | state vars ps => match ps with
 | proState x x0 x1 x2 x3 x4 x5 => state vars (proState (reverse x) x0 x1 x2 x3 x4 x5)
end
end. 

Reserved Notation " x '⟱'  x'"
                  (at level 40).
Definition DualState : Type := ((Statement*State) * (Statement* State)* Network). 
Print DualState. 
 Inductive DualEval : DualState -> DualState -> Prop :=
 (*
  | dulift : forall leftState rightState, 
       (getAction leftState) = reverse (getAction rightState) -> 
        DualEval ((OneProtocolStep leftState, leftState),(OneProtocolStep rightState, rightState) nil)
                 ((OneProtocolStep leftState, leftState),(OneProtocolStep rightState, rightState) nil)
                 *)
                 
  | duLeft : forall leftSTM leftState rightSTM rightState n leftState' n',
      (leftSTM , leftState, n) ⇒* (EndStatement, leftState', n') -> 
      ((leftSTM, leftState), (rightSTM,rightState), n) ⟱
               ( (OneProtocolStep (rever leftState'), rever leftState'),(rightSTM, rightState), n')
       
  | duRight : forall leftSTM leftState rightSTM rightState rightState' n n',
      (rightSTM , rightState, n) ⇒* (EndStatement, rightState', n') ->
      ((leftSTM,leftState), (rightSTM, rightState), n) ⟱
            ((leftSTM, leftState), (OneProtocolStep (rever rightState'), rever rightState'), n')
      
  (*| leftIsWait : forall leftSTM leftState rightSTM rightState n,
      DualEval (leftSTM, leftState) (rightSTM,rightState) n -> 
      forall leftState' n' stm',
      (leftSTM , leftState, n) ⇒⇒ (Wait >> stm', leftState', n') -> 
      forall n'' rightState',
      (rightSTM , rightState, n') ⇒⇒ (EndStatement, rightState', n'') ->
      DualEval (Wait >> stm', leftState') (OneProtocolStep (switchSendRec rightState'), (switchSendRec rightState')) n''
      
  | rightIsWait : forall leftSTM leftState rightSTM rightState n,
      DualEval (leftSTM, leftState) (rightSTM,rightState) n -> 
      forall rightState' n' stm',
      (rightSTM , rightState, n) ⇒⇒ (Wait >> stm', rightState', n') -> 
      forall n'' leftState',
      (leftSTM , leftState, n') ⇒⇒ (EndStatement, leftState', n'') ->
      DualEval (OneProtocolStep (switchSendRec leftState'), (switchSendRec leftState')) (Wait >> stm', rightState') n'' *)
      (* Those are wrong anyway. Well, not wrong, but we need more. What if the side not waiting goes to a stop?*)
      
  | duFinishLeftFirst : forall stmL stL stL' stmR stR stR' n n' n'',
      (stmL , stL, n) ⇒* (StopStatement, stL', n') ->
      (stmR, stR, n')  ⇒* (StopStatement, stR', n'') -> 
      DualEval ((stmL, stL), (stmR, stR), n) ((StopStatement,stL'), (StopStatement,stR'), n'') 
  | duFinishRightFirst : forall stmL stL stL' stmR stR stR' n n' n'',
      (stmR, stR, n)  ⇒* (StopStatement, stR', n') -> 
      (stmL , stL, n') ⇒* (StopStatement, stL', n'') -> 
      ((stmL, stL), (stmR, stR), n) ⟱ ((StopStatement,stL'), (StopStatement,stR'), n'')
       where "x '⟱' x' " := (DualEval x x').
      Hint Constructors DualEval.
Print MultiStep_stmEval. 


Inductive DualMultiStep :  DualState -> DualState -> Prop :=
 | dualmultistep_id : forall ds ds', ds ⟱  ds' -> DualMultiStep ds ds' 
 | dualmultistep_step : forall ds ds' ds'', 
    DualMultiStep ds ds' ->
    DualMultiStep ds'  ds'' ->
    DualMultiStep ds ds''.

Tactic Notation "step" := (eapply multistep_step; [constructor|]) || ( ((apply dualmultistep_step) || (eapply dualmultistep_step)) ; [constructor|]).


Ltac proto := match goal with 
 | [ |- _ ⇒* _] => step; [proto|]
 | [ |- (EffectStatement _ >>_,_,_) ⇒* _] => step; [c;c; (refl || auto)|]
 | [ |- context[ OneProtocolStep _]] => unfold OneProtocolStep; proto
 | [ |- context[ proto_handleIsMyTurnToSend _]] => unfold proto_handleIsMyTurnToSend; proto
 | [ |- context[ proto_handleNotMyTurnToSend _]] => unfold proto_handleNotMyTurnToSend; proto
 | [ |- context[ proto_handleCanSend _]] => unfold proto_handleCanSend; proto
 | [ |- context[ proto_handleCantSend _]] => unfold proto_handleCantSend; proto
 | [ |- context[ proto_handleNoNextDesire _]] => unfold proto_handleNoNextDesire; proto
 | [ |- context[ proto_handleExistsNextDesire _]] => unfold proto_handleExistsNextDesire; proto
 | [ H : evalChoose ?C ?T = false |- (IFS ?C THEN _ ELSE _,_,_) ⇒ _  ] => apply E_ChooseFalse; (progress auto)
 | [ |- (IFS ?C THEN _ ELSE _,_,_) ⇒ _  ] => (apply E_ChooseTrue; (reflexivity || assumption)) || (apply E_ChooseFalse; reflexivity)
 | [ |- (SendStatement (const constStop) _ _ >> _, _,_)  ⇒ (_,_,_)] => apply E_ChainBad; (apply E_SendStop) || (eapply E_SendStop)
 end.
 Hint Unfold OneProtocolStep proto_handleIsMyTurnToSend proto_handleNotMyTurnToSend. 

Theorem thm_canSendST_implies_handleExists : forall st, evalChoose CanSend st = true -> exists c, handleCompute compGetMessageToSend st = Some c.
Proof.
intros; simpl in H;  simpl; destruct st; simpl; destruct p; destruct (canSend l p0);  eauto;
inversion H. Qed.
Hint Resolve thm_canSendST_implies_handleExists.
Theorem thm_eval_1 : forall st n,
evalChoose IsMyTurntoSend st = true -> 
(OneProtocolStep st, st, n) ⇒ (proto_handleIsMyTurnToSend st, st, n).
Proof. intros. c. auto.
Qed.
Theorem thm_eval_0 : forall st n,
evalChoose IsMyTurntoSend st = false -> 
(OneProtocolStep st, st, n) ⇒ (proto_handleNotMyTurnToSend st, st, n).
Proof. intros. proto.
Qed.


Theorem thm_eval_11 : forall st n,
evalChoose IsAllGood st = true -> 
(proto_handleIsMyTurnToSend st, st, n) ⇒ (EffectStatement (effect_setAllGood Unset) >>
     (IFS QueuedRequestsExist THEN proto_handleCanSend st
      ELSE proto_handleCantSend st), st, n).
Proof. intros. c. auto.
Qed.

Theorem thm_eval_10 : forall st n,
evalChoose IsAllGood st = false -> 
(proto_handleIsMyTurnToSend st, st, n) ⇒ ( SendStatement (const constStop) (getMe st) (notMe (getMe st)) >> StopStatement, st, n).
Proof. intros. unfold proto_handleIsMyTurnToSend.  proto.
Qed.

Definition getAllGood (st : State) : AllGood :=
match st with
 | state vars ps => match ps with
    | proState x x0 x1 x2 x3 x4 x5 => x0
end
end. 

Lemma thm_allGood : forall st, evalChoose IsAllGood st = true -> getAllGood st = Yes.
Proof. intros. dest st. dest p. simpl in H. dest a0. simpl. auto.
inv H. inv H.
Qed.
Hint Resolve thm_allGood.

Theorem thm_ifwillthenway : forall st, evalChoose ExistsNextDesire st = true ->exists c,  handleCompute compGetNextRequest st = Some c .
    Proof.
    intros. destruct st. destruct p. destruct r.   simpl. exists constStop. intros. inversion H.
    simpl. destruct r. exists (constRequest d). auto. 
    Qed.





Theorem thm_onlyEffect_effects : forall (stm stm': Statement) (st st': State) (n n' : Network),
 (stm,st,n) ⇒ (stm',st',n') ->  
 getProState st = getProState st' \/ exists e, (headStatement stm) = EffectStatement e. 
Proof.
intro. induction stm ; try (intros; inversion H; left; reflexivity).
intros. simpl. left. inversion H. subst. destruct st.  auto. auto.
destruct st; auto.
intros. right. exists e. auto.
intros. left. inversion H; subst;   destruct st; auto.
intros; left; destruct st; inversion H; subst. auto.
simpl. 
intros; inversion H; subst.    eapply IHstm1.
eauto.
eapply IHstm1; eauto.
eapply IHstm1; eauto.
eapply IHstm1; constructor;  eauto.
Qed.
Hint Resolve thm_onlyEffect_effects.

Definition modifyState (a : AllGood) (st : State) : State :=
match st with
 | state vars ps => match ps with
 | proState x x0 x1 x2 x3 x4 x5 =>  state vars (proState x a x1 x2 x3 x4 x5)
end
end.
Definition modifyProState (a : AllGood) (ps : ProState) : ProState := 
match ps with
 | proState x x0 x1 x2 x3 x4 x5 => (proState x a x1 x2 x3 x4 x5)
end.

Theorem thm_noOneTouchesAction : forall stm stm' n n' st st', 
(stm,st,n) ⇒ (stm',st',n') -> getAction st = getAction st'.
Proof. intro. induction stm; intros;inv H; try (progress auto || destruct st; refl).
Focus 2. eapply IHstm1. apply H1.
Focus 2. eapply IHstm1. apply H1.
Focus 2. eapply IHstm1. apply H1.
destruct e; (s H1).  (destruct (varSubst t st)). destruct c. inv H1. inv H1. dest st. dest p.  auto.
inv H1. inv H1. destruct (varSubst t st); inv H1. dest st. dest p. destruct c.
simpl. destruct (reduceUnresolved d m r0). simpl. refl. refl. refl. refl.
destruct (varSubst t st). destruct c. inv H1. inv H1. dest st. dest p. refl.
inv H1. inv H1. inv H1. dest st. dest p. simpl. dest r. refl.
refl.
inv H1. inv H1. dest st. dest p. refl. destruct (varSubst t st). destruct c. inv H1.
dest st. dest p. s H1. destruct (getCounterReqItemFromPP p0 d). inv H1.
refl. inv H1. inv H1. inv H1.
inv H1. dest st. dest p.      refl.
Qed.
Theorem thm_noOneTouchesAction_m : forall stm stm' n n' st st', 
(stm,st,n) ⇒* (stm',st',n') -> getAction st = getAction st'.
Proof. intros. 
 dependent induction H. eapply thm_noOneTouchesAction. apply H.
erewrite IHMultiStep_stmEval1. eapply IHMultiStep_stmEval2.  auto. auto.
auto. auto.  
Qed.
(*
Theorem sending : forall stm' m n n' st st', 
(OneProtocolStep st ,st,n) ⇒* (SendStatement m (getMe st') (notMe (getMe st')) >> stm',st',n') -> getAction st' = ASend. intros. dependent induction H generalizing m.  inv H. destruct stm'0. 
eapply IHMultiStep_stmEval1. refl.  refl.  destruct stm'0. refl.      

 intros. inv H; auto. dest st. refl.
dest st.  refl. destruct effect. simpl in H1. destruct (varSubst t st). destruct c. inv H1. inv H1.
dest st. dest p. refl. inv H1. inv H1. simpl in H1. 
destruct (varSubst t st). inv H1. dest st. dest p. simpl.
simpl. destruct c. simpl. destruct (reduceUnresolved d m r0). simpl. refl.
simpl. refl. simpl. refl. simpl. refl.
inv H1. simpl in H1. destruct (varSubst t st). destruct c. inv H1. inv H1. simpl. dest st.
dest p. refl. inv H1. inv H1. simpl in H1. inv H1. dest st. dest p. simpl.
dest r.    refl. refl. dest st. simpl in H1. dest p. inv H1. refl. 
simpl in H1. destruct (varSubst t st). destruct c. inv H1. dest d. 
s H1. dest st. s H1. dest p. destruct (getCounterReqItemFromPP p0 (descriptor d)). inv H1.
refl . 
inv H1. inv H1. inv H1.
dest st. s H1. dest p. inv H1. refl. dest st. s H1. dest compTerm.
s H1. dest p. destruct (canSend l p0). inv H1. refl. inv H1.
refl. refl. dest st. refl.   (destruct (varSubst term2 st)). inv H1. refl.    refl.   
  refl.               dest p. refl.             dest H1.  simpl in H1.                  
simpl.         
simpl.             
auto. 
  refl.  simpl. dest p. refl.     

(            dest st. destruct p.  simpl in H1.  destruct H1 eqn:ef.  refl.   inv H1.    simpl.   simpl.  inv H.      *)

(*Theorem sending : forall st st' t n n' stm',
(OneProtocolStep st,st,n) ⇒* (SendStatement t (getMe st') (notMe (getMe st')) >> stm', st', n') -> getAction st = ASend.
Proof. intros.  destruct st. destruct p.
inv H. inv H1.  
 destruct a. simpl. refl.       
  -> 
(OneProtocolStep st,st,n) ⇒ (proto_handleIsMyTurnToSend st, st, n).
Proof. intros. inv H. inv H1.
inv H7. inv H1. inv H1.   
inv H2. inv H1. assumption.

exfalso.
inv H7. clear H2.
inv H4.
inv H5. inv H4.  
inv H11. inv H8. inv H9. inv H8.        
   inv H15. inv H12. inv H13. inv H12. inv H12. inv H16.
   apply endEval in H19. assumption. inv H12. inv H16. inv H12.
   inv H16. 
   inv H13. inv H12. inv H12. apply endEval in H19. assumption. inv H12. inv H17.
   inv H12. inv H17.                   

   dependent induction H. inv H.
eapply IHMultiStep_stmEval2. eauto.  
   inv H. exfalso.  inv H1.
inv H2. inv H1. apply H1.
exfalso.
inv H7. inv H4. inv H5. inv H4.     
*)
Theorem thm_receiveAlwaysFinishes : forall vars prst n m n', evalChoose IsMyTurntoSend (state vars prst) = false -> 
 receiveN n (getMe (state vars prst)) = Some (m, n') -> 
 m <> constStop ->  exists prst',
 (OneProtocolStep (state vars prst), (state vars prst), n) ⇒* (EndStatement, (state ((receivedMESSAGE,m)::vars) prst'), n').
Proof. intros. destruct m, prst. destruct (reduceUnresolved d m r0) eqn:unres. eexists. 
eapply multistep_step. c. unfold OneProtocolStep.
proto. step. unfold proto_handleNotMyTurnToSend. c. c. apply H0. auto.
step.  proto. c. c. c. simpl. rewrite unres.   refl.

eexists.
eapply multistep_step. c. unfold OneProtocolStep.
proto. step. unfold proto_handleNotMyTurnToSend. c. c. apply H0. auto.
step. proto.
 c. c. c.  simpl. rewrite unres.   reflexivity.

eexists.
eapply multistep_step. c. unfold OneProtocolStep.
proto. step. unfold proto_handleNotMyTurnToSend. c. c. apply H0. auto.
step. proto. simpl.
step. proto. c. c. c.  reflexivity.
nono H1.
Qed.



Lemma thm_mkAtt_and_App_have_rev_actions : forall ppP ppT reqls, 
 reverse(getAction(mkAttesterState ppT)) = getAction(mkAppraiserState ppP reqls).
Proof. intros; auto. Qed.
Hint Resolve thm_mkAtt_and_App_have_rev_actions.
Notation "x ⟱⟱  x'" := (DualMultiStep x x') (at level 35).
Hint Constructors DualMultiStep.


(* 
Theorem omegaProof : forall ppApp ppAtt reqLSApp n stL stR,
 stR = mkAttesterState ppAtt -> 
 stL = mkAppraiserState ppApp reqLSApp -> 
 (
 ((OneProtocolStep stL, stL), (OneProtocolStep stR, stR), n) ⟱⟱
 ((StopStatement,stL), (StopStatement, stR), n)   ) .
Proof. unfold mkAttesterState. unfold mkAppraiserState. unfold mkState. intros.
induction stR. 
induction stR, stL; subst. inversion H. subst. inversion H0. subst.
simpl. 
   , H0; subst.   

 subst.
eexists. eexists. exists nil. apply DualEval
inversion H. simpl in H0.     simpl in H.       destruct stL.    
Theorem final : exists stL stR n, 
DualEval (StopStatement,stL) (StopStatement, stR) n.
Proof. intros.   eexists. eexists. eexists.
econstructor.   
*)

Theorem thm_proto1 : forall st n, evalChoose IsMyTurntoSend st = true -> 
 (OneProtocolStep st, st, n) ⇒ (proto_handleIsMyTurnToSend st, st, n).
Proof. intros. constructor; auto.
Qed.
Theorem thm_proto0 : forall st n, evalChoose IsMyTurntoSend st = false -> 
 (OneProtocolStep st, st, n) ⇒ (proto_handleNotMyTurnToSend st, st, n).
Proof. intros. constructor; auto.
Qed.

Theorem thm_onlySendOrReceiveChangesNetwork : forall (stm stm': Statement) (st st': State) (n n' : Network),
 (stm,st,n) ⇒ (stm',st',n') -> 
 n = n' \/
 (exists t p1 p2, headStatement stm = SendStatement t p1 p2) \/
 (exists vid, headStatement stm = ReceiveStatement vid)
 .
 Proof. intro; induction stm; intros; try (right; left; exists t; exists p; exists p0; reflexivity) ||
 (try (left; inversion H; subst; reflexivity)).
 inversion H; subst.
 right. right; exists v; auto.
 left; reflexivity.
 right; right; exists v; auto.
 inversion H; subst.
 eauto.
 eauto.
 eauto.
 eauto.
 Qed.

(*
Theorem receiveTurnAlwaysFinishes : forall st n,  
 evalChoose IsMyTurntoSend st = false ->  exists st' n', 
 (OneProtocolStep st,st,n) ⇒⇒ (EndStatement,st',n') \/
 (OneProtocolStep st,st,n) ⇒⇒ (StopStatement,st',n').
Proof. intros. destruct (receiveN n (getMe st)) eqn:recstat. destruct p. destruct c.
 eexists. eexists.
 left.  eapply multistep_step. constructor. apply E_ChooseFalse. auto.
        eapply multistep_step. unfold proto_handleNotMyTurnToSend.  constructor. constructor. constructor.
        apply recstat. nono.  auto.
*)

 


Fixpoint mostRecentFromMe (st : State) (n : Network) : bool :=
match n with
 | nil => false
 | cons m nil => match m with
    | networkMessage f _ _ => if (eq_dec_Participant f (getMe st)) then true else false
    end
 | cons _ ls => mostRecentFromMe st ls
end. 
 

 
 Theorem thm_evalSendTurn : forall  st n, (evalChoose IsMyTurntoSend st) = true -> (OneProtocolStep st ,st,n) ⇒ (proto_handleIsMyTurnToSend st, st, n).
Proof.
intros; unfold OneProtocolStep; constructor; assumption.
Qed.
Hint Resolve thm_evalSendTurn. 

Theorem thm_evalReceiveTurn : forall st n, (evalChoose IsMyTurntoSend st) = false -> (OneProtocolStep st ,st,n) ⇒ (proto_handleNotMyTurnToSend st, st, n).
Proof. intros; unfold OneProtocolStep; constructor; assumption.
Qed.
Hint Resolve thm_evalReceiveTurn.

Theorem thm_eval_existsNextDesire : forall st n, (evalChoose ExistsNextDesire st) = true -> 
(evalChoose IsAllGood st) = true ->  
(proto_handleCantSend st, st, n) ⇒
 (proto_handleExistsNextDesire st, st, n)
.
Proof. intros; unfold proto_handleIsMyTurnToSend. cca.
Qed.
Hint Resolve thm_eval_existsNextDesire.

Print OneProtocolStep. 

Theorem thm_eval_NoNextDesire : forall st n, (evalChoose ExistsNextDesire st) = false -> (proto_handleCantSend st, st, n) ⇒ 
 (proto_handleNoNextDesire st, st, n)
.
Proof. intros; unfold proto_handleIsMyTurnToSend; constructor; assumption.
Qed.
Hint Resolve thm_eval_NoNextDesire.

Theorem thm_sendTurnHelper : forall st, isMyTurn st = true -> evalChoose IsMyTurntoSend st = true.
Proof.
intros. destruct st. destruct p. auto. Qed.
Hint Resolve thm_sendTurnHelper.

Theorem thm_varSubstConst : forall st c, varSubst (const c) st = Some c.
Proof. intros. destruct st. destruct v. auto. auto.
Qed.
Hint Resolve thm_varSubstConst.

Hint Unfold OneProtocolStep.
Hint Unfold proto_handleCanSend.
Hint Unfold proto_handleCantSend.
Hint Unfold proto_handleNoNextDesire.
Hint Unfold proto_handleIsMyTurnToSend.
Hint Unfold proto_handleNotMyTurnToSend.
Hint Unfold proto_handleExistsNextDesire.  



(*(EndStatement, assign toSendMESSAGE x (state v p), sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) x n)
⇒⇒ (EndStatement, st', n')
*)
(*

*)
Theorem thm_sendOnNetworkAppends : forall  f t c n, length (sendOnNetwork f t c n) = length n + 1.
Proof. intros. induction n.
auto.
simpl. auto.
Qed.
Hint Resolve thm_sendOnNetworkAppends.         
Require Import Omega. 

Theorem thm_receiveWhenStop : forall n vid v p n',
receiveN n (getMe (state v p)) = Some (constStop, n') ->
(ReceiveStatement vid, (state v p), n) ⇒ 
(StopStatement,assign vid constStop (state v p), n').
Proof. intros.  eapply E_ReceiveStop. assumption.
Qed.

Theorem thm_oneStepProtoStopsWhenTold :forall v p n n', evalChoose IsMyTurntoSend (state v p) = false -> 
receiveN n (getMe (state v p)) = Some (constStop, n') -> 
((OneProtocolStep (state v p) , (state v p), n) ⇒* (StopStatement, assign receivedMESSAGE constStop (state v p), n')) .
Proof. intros.
eapply multistep_step. constructor. apply E_ChooseFalse. auto.
constructor. constructor. apply thm_receiveWhenStop. auto.
Qed.

Definition getPrivacy (st : State) : PrivacyPolicy :=
match st with
 | state _ ps => match ps with
    | proState _ _ _ pp _ _ _ => pp
end
end.
SearchAbout PrivacyPolicy.


Theorem thm_isRemovedFromPrivacyhandleST : forall st d, 
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
Hint Resolve thm_isRemovedFromPrivacyhandleST.

Theorem thm_isRemovedFromPrivacy : forall st st' n t d, 
  varSubst t st = Some (constRequest d) -> 
  (EffectStatement (effect_ReducePrivacyWithRequest t), st, n) ⇒ (Skip, st',n) -> 
  findandMeasureItem (getPrivacy st') d = None.
Proof. intros. inversion H0; subst.
simpl in H2. rewrite H in H2. inversion H2. subst. 
Theorem x : forall d st, findandMeasureItem (getPrivacy (rm_f_Privacy_w_RequestST d st)) d = None.
intros. destruct st. simpl. destruct p. simpl. auto. Qed. apply x. 
Qed.

Definition OneProtocolStep2 (st : State) : Statement :=
IFS IsMyTurntoSend THEN
  IFS IsAllGood THEN
    EffectStatement (effect_setAllGood Unset) >>
    IFS QueuedRequestsExist THEN 
      IFS CanSend THEN 
        Compute toSendMESSAGE compGetMessageToSend >>
        SendStatement (variable toSendMESSAGE) (getMe st) (notMe (getMe st)) >> 
        Compute (variden 1) compGetfstQueue >>
        EffectStatement (effect_ReducePrivacyWithRequest (variable (variden 1))) >>
        EffectStatement effect_rmFstQueued >>
        EffectStatement (effect_setAllGood Yes) >> (*all good here! *)
        EndStatement
      ELSE (*Can't send and queued request exists *)
        EffectStatement (effect_setAllGood No) >> (* no, this is bad! *) 
        SendStatement (const constStop) (getMe st) (notMe (getMe st)) >> 
        StopStatement (*Give up!*)
    ELSE (*No queued up things for me. So I can continue down my list of things I want. *)
      IFS ExistsNextDesire THEN 
        Compute toSendMESSAGE compGetNextRequest >>
        EffectStatement effect_MvFirstDesire >> 
        SendStatement (variable toSendMESSAGE) (getMe st) (notMe (getMe st)) >> 
        EffectStatement (effect_setAllGood Yes) >>
        EndStatement
      ELSE (* I must send, nothin queued, nothin left I want, quit! *)
        EffectStatement (effect_setAllGood Yes) >> (*all is well, just out! *)
        SendStatement (const constStop) (getMe st) (notMe (getMe st)) >> 
        StopStatement
  ELSE
    SendStatement (const constStop) (getMe st) (notMe (getMe st)) >>
    StopStatement      
ELSE
  ReceiveStatement (receivedMESSAGE) >>
  IFS (IsMeasurement (variable (receivedMESSAGE))) THEN 
    EffectStatement (effect_ReduceStatewithMeasurement (variable (receivedMESSAGE)) ) >>   
    EndStatement
  ELSE
    IFS (IsRequest (variable (receivedMESSAGE))) THEN 
      EffectStatement (effect_StoreRequest (variable (receivedMESSAGE))) >> EndStatement
    ELSE (*we must have received a stop *)
      StopStatement.
Example xx : forall st, OneProtocolStep st = OneProtocolStep2 st. 
intros. auto. Qed.
