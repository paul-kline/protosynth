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
Require Import MyShortHand. 

(*Require Import String.*) 
(*
Require Import Coq.Relations.Relation_Definitions.
*)
(*Add LoadPath "/users/paulkline/Documents/coqs/dependent-crypto".
Add LoadPath "/users/paulkline/Documents/coqs/cpdt/src".
Add LoadPath "C:\Users\Paul\Documents\coqs\dependent-crypto".
Add LoadPath "C:\Users\Paul\Documents\coqs\cpdt\src". *)
Add LoadPath "C:\Users\Paul\Documents\coqStuff\protosynth". 
Require Import ProtoSynthDataTypes. 
Require Import ProtoSynthDataTypeEqualities.
Require Import ProtoSynthProtocolDataTypes. 
Require Import Coq.Lists.List.
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
Search bool. 
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
 simpl; exact true. 
 Defined.
 

 


 
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
Theorem findAndMeasureItemL : forall pp d d0 val x, findandMeasureItem pp d = Some (constValue d0 val, x) -> d = d0.
Proof. intros. induction pp.  inv H.
destruct r. simpl in H. destruct (eq_dec_Description d1 d). subst. inv H.
apply IHpp. assumption.
simpl in H. destruct (eq_dec_Description d1 d). subst. inv H. subst. refl.
apply IHpp. assumption.
simpl in H. destruct (eq_dec_Description d1 d). subst. inv H. apply IHpp. assumption.
simpl in H.  destruct (eq_dec_Description d1 d). subst. inv H. apply IHpp. assumption.
simpl in H.  destruct (eq_dec_Description d1 d). subst. inv H. apply IHpp. assumption.
Qed.
Hint Resolve findAndMeasureItemL.
 
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
Definition snd3 {A B C : Type} (x : (A*B*C) ): B := match x with 
 | (_,b,_) => b
 end. 
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
*)
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
     | proState a g p pp b unres dls => match(handleRequest' pp d) with 
                                | (pp',c,ri) => state ((toSendMESSAGE,c)::vars) (proState a g p pp' b (ConsRequestLS ri unres) dls)
                                                  
                              end
end
end. 

 (* ls is the list of DESCRIPTIONS requested from me. This function is used when it is
 your turn to send something, and tells whether or not you can send the measurement of the request. You may not be able to because you have nothing left to request. (nil). 
 Your privacy policy allows for you to send the requested measurement.
  Possible reasons for failure:
 1.   The request is an unsatifiable object from the privacy policy. 
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

Theorem handleReqL : forall pp ls d, handleRequest' pp d = 
Theorem canSendL : forall pp ls d, (canSend ls pp = Some d )-> (head ls) =Some  d.
Proof. intros. destruct ls. inv H. rewrite <- H.
simpl. destruct (handleRequest' pp d0). destruct p. destruct c.
simpl.           

Definition canSendST (st : State) : option Description :=
match st with
 | state vars prostate => match prostate with
                           | proState _ _ _ pp _ _ ls =>  canSend ls pp
                          end
end.


Definition assign (var : VarID) (val : Const) (st : State) :=
  match st with
 | state varls prostate => state ((var,val)::varls) prostate
end. 

Definition isMyTurn (st : State) : bool :=
match st with
 | state vs ps => (match ps with
     | proState a _ _ _ _ _ _ => (match a with
                                 | ASend => true
                                 | AReceive => false
                                end)
     end)
end.
Definition queuedRequestsExist (st : State) := 
match st with
 | state vs ps => match ps with
       | proState _ _ _ _ _ _  nil => false
       | proState _ _ _ _ _ _ _ => true
        end

 end. 
Definition existsNextDesire (st : State) :=
match st with
 | state _ ps =>match ps with
            | proState _ _ _ _ wants _ _ =>match wants with
                             | emptyRequestLS => false
                             | ConsRequestLS x x0 => true
                            end
            end
end.

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
auto. omega.```          
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
                        | proState _ _ p _ _ _ _ => p
end

end.

Definition mvNextDesire (st : State) : State :=
match st with
 | state vars ps =>match ps with
            | proState a g b c wants e f =>(match wants with
                   | emptyRequestLS => state vars (proState a g b c 
                      emptyRequestLS e f)
                   | ConsRequestLS ri rest => state vars (proState a g b c rest
                      (ConsRequestLS ri e) f )
                  end) 
            end
end.

Definition storeRequest (d : Description) (st : State) : State :=
match st with
 | state vs ps => match ps with
      | proState x g x0 x1 x2 x3 queue => state vs (proState  x g x0 x1 x2 x3 (d :: queue))
end
end. 

Definition reducePrivacy_w_RequestST (d : Description) (st : State) : State :=
match st with
 | state vs ps => match ps with
      | proState x g x0 pp x2 x3 x4 => state vs (proState x g x0 (rmAllFromPolicy pp d) x2 x3 x4)
     end
end. 

Definition handleRmFstQueued (st : State) :=
match st with
 | state vs ps => match ps with
    | proState x g x0 x1 x2 x3 x4 => state vs
       (proState x g x0 x1 x2 x3 (tail x4)) 
end
end. 

Fixpoint rmFromPP (pp : PrivacyPolicy) (d : Description) :=
match pp with
 | EmptyPolicy => EmptyPolicy
 | @ConsPolicy dp x x0 => if (eq_dec_Description d dp) then  rmFromPP x0 d 
                                                       else  @ConsPolicy dp x (rmFromPP x0 d)
end. 
Fixpoint getCounterReqItemFromPP (pp : PrivacyPolicy) (d : Description) : option RequestItem :=
match pp with
 | EmptyPolicy => None
 | @ConsPolicy dp x x0 => if (eq_dec_Description d dp) then match x with
 | @rule _ dd  r => Some (requestItem dd r)
 | free _ => None
 | never _ => None
 | multiReqAnd _ _ x0 => None
 | multiReqOr _ _ x0 => None
end 
                                                       else  (getCounterReqItemFromPP x0 d)
end. 
Definition handlecp_ppUnresolved (d : Description)  (st : State) : option State := 
match st with
 | state vs ps => match ps with
    | proState x g x0 pp x2 x3 x4 => match  getCounterReqItemFromPP pp d with 
                                      | None => None
                                      | Some reqI => Some (state vs (proState x g x0 pp x2 (ConsRequestLS reqI x3) x4))
                                      end
end
end. 

Definition handleSetAllGood (g : AllGood) (st : State) : State:=
match st with
 | state var ps => match ps with
          | proState x x0 x1 x2 x3 x4 x5 => state var (proState x g x1 x2 x3 x4 x5) 
end
end.
 
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
                                        | Some (constRequest r) => Some (reducePrivacy_w_RequestST r st)
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
 | effect_setAllGood x  => Some (handleSetAllGood x st)
end. 


Check measure. 
Definition getNextDesire (st : State) : option Description :=
match st with
 | state _ ps =>match ps with
            | proState _ _ _ _ wants _ _ =>(match wants with
                             | emptyRequestLS => None
                             | ConsRequestLS ri _ => (match ri with
                                         | requestItem d x => Some d
                                        end)

                            end)
            end
end.

Definition handleGetfstQueue (st : State) :=
match st with
 | state _ ps => match ps with
    | proState x g x0 x1 x2 x3 x4 => match x4 with
 | nil => None
 | cons x x0 => Some (constRequest x)
end
end
end.

Definition handleCompute (comp : Computation) (st : State) : option Const :=
 match comp with
  | compGetfstQueue => handleGetfstQueue st
  | compGetMessageToSend => match (canSendST st) with 
                              | Some d => Some (constValue d (measure d))
                              | None => None
                            end
  | compGetNextRequest =>  (match (getNextDesire st) with 
                              | None => None
                              | Some desire => Some (constRequest desire)
                            end)
 end.

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

Inductive MultiStep_stmEval : (Statement * State * Network) -> (Statement * State * Network) -> Prop := 
| multistep_id : forall stm st n stm' st' n', stmEval (stm,st,n) (stm',st',n') -> MultiStep_stmEval (stm,st,n) (stm',st',n')
| multistep_step :  forall stm st n stm' st' n' stm'' st'' n'', 
MultiStep_stmEval (stm,st,n) (stm',st',n') -> 
MultiStep_stmEval (stm',st',n') (stm'',st'',n'') -> 
MultiStep_stmEval (stm,st,n) (stm'',st'',n'').

Notation "x ⇓⇓ x'" := (MultiStep_stmEval x x') (at level 35).
 
Hint Constructors MultiStep_stmEval. 



Definition notMe (p : Participant) : Participant :=
match p with
 | ATTESTER => APPRAISER
 | APPRAISER => ATTESTER
end.
Definition proto_handleCanSend (st : State) :=
 IFS CanSend
    THEN Compute toSendMESSAGE compGetMessageToSend >>
         SendStatement (variable toSendMESSAGE) (getMe st) (notMe (getMe st)) >> 
         Compute (variden 1) compGetfstQueue >>
         EffectStatement (effect_ReducePrivacyWithRequest (variable (variden 1))) >>
         EffectStatement effect_rmFstQueued >>
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
       | proState a g b c d e f => state vars (proState (reverse a) g b c d e f)
      end

  end. 
  Definition getAction ( st : State) : Action := 
  match st with
   | state vars ps=> match ps with
       | proState a g b c d e f => a
      end
  end. 
  (*⇓
  U+21af ⇊
  ↡ ⍗ *)
  Definition rever (st : State) : State := 
match st with
 | state vars ps => match ps with
 | proState x x0 x1 x2 x3 x4 x5 => state vars (proState (reverse x) x0 x1 x2 x3 x4 x5)
end
end. 


Ltac proto := match goal with 
 | [ |- context[ OneProtocolStep _]] => unfold OneProtocolStep; proto
 | [ H : evalChoose ?C ?T = false |- (IFS ?C THEN _ ELSE _,_,_) ⇓ _  ] => apply E_ChooseFalse; (progress auto)
 | [ |- (IFS ?C THEN _ ELSE _,_,_) ⇓ _  ] => (apply E_ChooseTrue; (reflexivity || assumption)) || (apply E_ChooseFalse; reflexivity)
 end.
 Hint Unfold OneProtocolStep proto_handleIsMyTurnToSend proto_handleNotMyTurnToSend. 
Tactic Notation "step" := eapply multistep_step; [constructor|].

Theorem canSendST_implies_handleExists : forall st, evalChoose CanSend st = true -> exists c, handleCompute compGetMessageToSend st = Some c.
Proof.
intros; simpl in H;  simpl; destruct st; simpl; destruct p; destruct (canSend l p0);  eauto;
inversion H. Qed.
Hint Resolve canSendST_implies_handleExists.
Theorem eval_1 : forall st n,
evalChoose IsMyTurntoSend st = true -> 
(OneProtocolStep st, st, n) ⇓ (proto_handleIsMyTurnToSend st, st, n).
Proof. intros. c. auto.
Qed.
Theorem eval_0 : forall st n,
evalChoose IsMyTurntoSend st = false -> 
(OneProtocolStep st, st, n) ⇓ (proto_handleNotMyTurnToSend st, st, n).
Proof. intros. proto.
Qed.


Theorem eval_11 : forall st n,
evalChoose IsAllGood st = true -> 
(proto_handleIsMyTurnToSend st, st, n) ⇓ (EffectStatement (effect_setAllGood Unset) >>
     (IFS QueuedRequestsExist THEN proto_handleCanSend st
      ELSE proto_handleCantSend st), st, n).
Proof. intros. c. auto.
Qed.

Theorem eval_10 : forall st n,
evalChoose IsAllGood st = false -> 
(proto_handleIsMyTurnToSend st, st, n) ⇓ ( SendStatement (const constStop) (getMe st) (notMe (getMe st)) >> StopStatement, st, n).
Proof. intros. unfold proto_handleIsMyTurnToSend.  proto.
Qed.

Definition getAllGood (st : State) : AllGood :=
match st with
 | state vars ps => match ps with
    | proState x x0 x1 x2 x3 x4 x5 => x0
end
end. 

Lemma allGood : forall st, evalChoose IsAllGood st = true -> getAllGood st = Yes.
Proof. intros. dest st. dest p. simpl in H. dest a0. simpl. auto.
inv H. inv H.
Qed.
    
Theorem eval1 : forall st v (n: Network) a allg part pp rls unres l,
st = state v (proState a allg part pp rls unres l) -> 
evalChoose IsAllGood st         = true ->
evalChoose IsMyTurntoSend st     = true -> 
evalChoose QueuedRequestsExist st= true ->
evalChoose CanSend st            = true -> exists d  p0,   
 (OneProtocolStep st, st, n) ⇓⇓ (EndStatement,state ((variden 1, constRequest d) :: (toSendMESSAGE, constValue d (measure d)) :: v) (proState a Unset part (rmAllFromPolicy p0 d) rls unres (tail l)) ,sendOnNetwork (getMe st) (notMe (getMe st)) (constValue d (measure d)) n).
Proof. intros. apply allGood in H0. subst. simpl. simpl in H0. subst.

destruct (canSend l pp) eqn:fff.
destruct l. simpl in fff. inv fff.

eexists. eexists.
step. unfold OneProtocolStep. proto.
step. unfold proto_handleIsMyTurnToSend.  proto.
step. c. c. simpl. refl.
step. proto.
step. unfold proto_handleCanSend.  proto.
simpl.  step. c. c. simpl. simpl in fff.  rewrite fff. refl.
step. c. c. simpl. refl. nono.
step. c. c. simpl. refl. 
step. c. c. simpl. refl.
step. c. c. simpl. refl.
c. 
Lemma fef : forall d0 l pp d, canSend (d0 :: l) pp = Some d -> d0 =d .
Proof. intros. simpl in H.   induction pp. simpl in H. inv H.
simpl in H. destruct (eq_dec_Description d1 d0). destruct r.
inv H. subst. inv H. refl. inv H. inv H. inv H.
destruct (findandMeasureItem pp d0). destruct p. destruct c. subst. inv H.
subst.
apply IHpp. simpl.                      simpl in H.    
apply E_End.  c.  
step. c. c. simpl. refl.
c. apply E_End.  c.                 step.  
   refl.              proto.    

     destruct (canSend l pp). refl.  step. c. c. simpl.   refl.     c.    proto.               apply E_ChooseTrue. assumption.    proto.    

      unfold OneProtocolStep.
assert (evalChoose CanSend st = true). assumption. destruct l. 
apply canSendST_implies_handleExists in H3. destruct H3. 
exists x. destruct x.  eexists. eexists. eexists.  
eapply multistep_step. cca.
unfold proto_handleIsMyTurnToSend.
step. c. auto.
step. c. c. refl.
step. 
c. simpl. subst.   auto.
step. c. simpl. subst.   auto.
 simpl.
step. c. c. subst. apply H3. subst. 
step. c. c. subst. simpl. refl. nono. simpl in H4.  simpl in H2.    inv H2.


eexists. eexists. eexists.   
eapply multistep_step. cca.
unfold proto_handleIsMyTurnToSend.
step. c. auto.
step. c. c. refl.
step. 
c. simpl. subst.   auto.
step. c. simpl. subst.   auto.
 simpl.
step. c. c. subst. apply H3. subst. 
step. c. c. subst. simpl. refl. nono. simpl in H4.  simpl in H2.    inv H2.

eexists. eexists. eexists.   
eapply multistep_step. cca.
unfold proto_handleIsMyTurnToSend.
step. c. auto.
step. c. c. refl.
step. 
c. simpl. subst.   auto.
step. c. simpl. subst.   auto.
 simpl.
step. c. c. subst. apply H3. subst. 
step. c. c. subst. simpl. refl. nono. simpl in H4.  simpl in H2.    inv H2.


step. c. c. simpl. simpl in H3. inv H3.
simpl in H3. inv H3.

eexists. eexists. eexists. eexists. subst.     
eapply multistep_step. cca.
unfold proto_handleIsMyTurnToSend.
step. c. auto.
step. c. c. refl.
step. 
c. simpl. subst.   auto.
step. c. simpl. subst.   auto.
 simpl.
step. c. c. subst. simpl.  apply H3. subst. 
step. c. c. subst. simpl. refl. nono. simpl in H4.  simpl in H2.    inv H2.


     refl.
step. c. c. simpl. refl.
step. c. c. simpl. refl.
c. simpl. simpl. constr.   eapply E_End.    c.                
simpl in H3. 
simpl in H4. 
destruct (canSend l p0). inv H5. nono.
inv H5.
destruct l. destruct p0.
step. c. c. simpl. simpl in H3.  simpl in H3. inv H3. 
 simpl in H3. inv H3.
step. c. c. simpl. simpl in H3. inv H3.
step. c. c.  simpl.        
simpl in H3. inv H3.
simpl in H3. inv H3.
simpl.
step. c. c. simpl. refl.
step. c. c. simpl. refl.
step. c. c. simpl. refl.
c.  c.           


 
        
simpl in H3.     
evalChoose CanSend st ->   
  refl. 
simpl in H3.    
simpl in H3.      destruct l.      
nono H5.          
c.  simpl in H3. simpl in H2.


rewrite H. 
simpl in H. 
simpl. 
simpl in H.        destruct (canSend l0 p1). simpl.   destruct l0. simpl. refl.
simpl. simpl in H.       


Proof. intros. si 
Lemma canSendM : forall v a a0 p p1 r r0 l0 m, 
evalChoose CanSend (state v (proState a a0 p p1 r r0 l0)) = true-> 
canSend l0 p1 = Some (snd3 (handleRequest'.
Proof. intros. simpl in H. destruct l0. simpl. simpl in H. inv H. simpl in H.
simpl.  .     destruct (canSend l0 p1) eqn:eifj. simpl.       
 destruct (canSend l p0). step. c. c. apply H2.
simpl. step. c. c. simpl. refl.      

simpl. refl.  eauto.   rewrite H3.   destruct l.     auto. 
c.   
proto. 
eapply bigstep_stm_step. constructor. 
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
reduceStateWithMeasurement (constValue d c) (assign receivedMESSAGE (constValue d c) (state v p)) = pp' -> 
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
(OneProtocolStep (state v p), (state v p), n) ⇓⇓ (EndStatement, (storeRequest r (assign receivedMESSAGE (constRequest r) (state v p))), tail n).
Proof. intros. unfold OneProtocolStep.
 intros. 
eapply bigstep_stm_step. cca.
eapply bigstep_stm_step. autounfold. constructor. constructor. Print E_Receive.  constructor.  apply H0.  unfold not. intros. inv H1.
eapply bigstep_stm_step. constructor. apply E_ChooseFalse. simpl. destruct p. auto.
eapply bigstep_stm_step.    constructor. constructor. simpl. destruct p. auto.
eapply bigstep_stm_step. cca.
constructor. constructor.
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
      (leftSTM , leftState, n) ⇓⇓ (EndStatement, leftState', n') -> 
      ((leftSTM, leftState), (rightSTM,rightState), n) ⟱
               ( (OneProtocolStep (rever leftState'), rever leftState'),(rightSTM, rightState), n')
       
  | duRight : forall leftSTM leftState rightSTM rightState rightState' n n',
      (rightSTM , rightState, n) ⇓⇓ (EndStatement, rightState', n') ->
      ((leftSTM,leftState), (rightSTM, rightState), n) ⟱
            ((leftSTM, leftState), (OneProtocolStep (rever rightState'), rever rightState'), n')
      
  (*| leftIsWait : forall leftSTM leftState rightSTM rightState n,
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
      DualEval (OneProtocolStep (switchSendRec leftState'), (switchSendRec leftState')) (Wait >> stm', rightState') n'' *)
      (* Those are wrong anyway. Well, not wrong, but we need more. What if the side not waiting goes to a stop?*)
      
  | duFinishLeftFirst : forall stmL stL stL' stmR stR stR' n n' n'',
      (stmL , stL, n) ⇓⇓ (StopStatement, stL', n') ->
      (stmR, stR, n')  ⇓⇓ (StopStatement, stR', n'') -> 
      DualEval ((stmL, stL), (stmR, stR), n) ((StopStatement,stL'), (StopStatement,stR'), n'') 
  | duFinishRightFirst : forall stmL stL stL' stmR stR stR' n n' n'',
      (stmR, stR, n)  ⇓⇓ (StopStatement, stR', n') -> 
      (stmL , stL, n') ⇓⇓ (StopStatement, stL', n'') -> 
      ((stmL, stL), (stmR, stR), n) ⟱ ((StopStatement,stL'), (StopStatement,stR'), n'')
       where "x '⟱' x' " := (DualEval x x').
      Hint Constructors DualEval.
Print MultiStep_stmEval. 
Inductive DualMultiStep :  DualState -> DualState -> Prop :=
 | dualmultistep_id : forall ds ds', ds ⟱  ds' -> DualMultiStep ds ds' 
 | dualmultistep_step : forall ds1 ds1' ds2 ds2', 
    ds1 ⟱  ds1' ->
    ds2 ⟱  ds2' ->
    DualMultiStep ds1 ds2'.
    



Theorem onlyEffect_effects : forall (stm stm': Statement) (st st': State) (n n' : Network),
 (stm,st,n) ⇓ (stm',st',n') ->  
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
Hint Resolve onlyEffect_effects.

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

Theorem receiveAlwaysFinishes : forall vars prst n m n', evalChoose IsMyTurntoSend (state vars prst) = false -> 
 receiveN n (getMe (state vars prst)) = Some (m, n') -> 
 m <> constStop ->  exists prst',
 (OneProtocolStep (state vars prst), (state vars prst), n) ⇓⇓ (EndStatement, (state ((receivedMESSAGE,m)::vars) prst'), n').
Proof. intros. destruct m, prst. destruct (reduceUnresolved d m r0) eqn:unres. eexists. 
eapply multistep_step. c. unfold OneProtocolStep.
proto. step. unfold proto_handleNotMyTurnToSend. c. c. apply H0. auto.
step.  proto.
step. c. c. simpl.  reflexivity.
rewrite unres. c. apply E_End.

eexists.
eapply multistep_step. c. unfold OneProtocolStep.
proto. step. unfold proto_handleNotMyTurnToSend. c. c. apply H0. auto.
step. proto.
step. c. c. simpl.  reflexivity.
rewrite unres. c. apply E_End.

eexists.
eapply multistep_step. c. unfold OneProtocolStep.
proto. step. unfold proto_handleNotMyTurnToSend. c. c. apply H0. auto.
step. proto. simpl.
step. proto. step. c. c. reflexivity.  
 simpl.
 c. c.
nono H1.
Qed.



Lemma mkAtt_and_App_have_rev_actions : forall ppP ppT reqls, 
 reverse(getAction(mkAttesterState ppT)) = getAction(mkAppraiserState ppP reqls).
Proof. intros; auto. Qed.

Notation "x ⟱⟱  x'" := (DualMultiStep x x') (at level 35).
Hint Constructors DualMultiStep. 
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

Theorem receiveAlwaysSetsAllGood : forall vars prst prst' n m n', evalChoose IsMyTurntoSend (state vars prst) = false -> 
 (OneProtocolStep (state vars prst), (state vars prst), n) ⇓⇓ (EndStatement, (state ((receivedMESSAGE,m)::vars) prst'), n') -> 
 prst' = modifyProState Yes prst \/ prst' = modifyProState No prst. 
Proof. intros.  
specialize receiveAlwaysFinishes with (vars:= vars) (prst:=prst)(n:=n)(m:=m)(n':=n').
intros. 
 . .  in H0.  
left.
eapply bigstep_stm_step. constructor. apply E_ChooseFalse. auto.
eapply bigstep_stm_step. constructor. constructor. constructor. apply H0. assumption.
destruct m eqn:whatism. 
eapply bigstep_stm_step. constructor. constructor. simpl. destruct prst.  auto.
simpl. destruct prst.  destruct (reduceUnresolved d m0 r0) eqn:unres. eapply bigstep_stm_step.
simpl. constructor. constructor. simpl.  constructor. simpl. rewrite unres.        
 reflexivity. constructor. econstructor.  eauto.  
eapply bigstep_stm_step. constructor. constructor. simpl.  auto.    constructor.
simpl.
rewrite unres. reflexivity.  constructor. eauto.  constructor.  .  
destruct (reduceUnresolved d m r0) eqn:unres.
simpl. reflexivity. simpl. rewrite unres. auto. 
destruct (reduceUnresolved d m r0) eqn:unres.
simpl. reflexivity. simpl. rewrite unres. auto.               auto.       constructor; auto.    
constructor.   constructor; auto.              auto.       constructor; auto.    
constructor.   constructor; auto.
Qed.
Theorem proto1 : forall st n, evalChoose IsMyTurntoSend st = true -> 
 (OneProtocolStep st, st, n) ⇓ (proto_handleIsMyTurnToSend st, st, n).
Proof. intros. constructor; auto.
Qed.
Theorem proto0 : forall st n, evalChoose IsMyTurntoSend st = false -> 
 (OneProtocolStep st, st, n) ⇓ (proto_handleNotMyTurnToSend st, st, n).
Proof. intros. constructor; auto.
Qed.

Theorem proto11 : forall st n, evalChoose IsAllGood st = true -> 
 (proto_handleIsMyTurnToSend st, st, n) ⇓ (proto_handleCanSend st, st, n).
Proof. intros. unfold proto_handleIsMyTurnToSend. eapply E_ChooseTrue.  constructor; auto.
Qed.

     unfold OneProtocolStep.  eapply E_ChooseTrue.   constructor. eauto.  auto.    


Theorem receiveTurnAlwaysFinishes : forall st n,  
 evalChoose IsMyTurntoSend st = false ->  exists st' n', 
 (OneProtocolStep st,st,n) ⇓⇓ (EndStatement,st',n') \/
 (OneProtocolStep st,st,n) ⇓⇓ (StopStatement,st',n').
Proof. intros. destruct (receiveN n (getMe st)) eqn:recstat. destruct p. destruct c.
 eexists. eexists.
 left.  eapply bigstep_stm_step. constructor. apply E_ChooseFalse. auto.
        eapply bigstep_stm_step. unfold proto_handleNotMyTurnToSend.  constructor. constructor. constructor.
        apply recstat. nono.  auto. 
Theorem onlySendOrReceiveChangesNetwork : forall (stm stm': Statement) (st st': State) (n n' : Network),
 (stm,st,n) ⇓ (stm',st',n') -> 
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
 


Fixpoint mostRecentFromMe (st : State) (n : Network) : bool :=
match n with
 | nil => false
 | cons m nil => match m with
    | networkMessage f _ _ => if (eq_dec_Participant f (getMe st)) then true else false
    end
 | cons _ ls => mostRecentFromMe st ls
end. 
 

 
 Theorem evalSendTurn : forall  st n, (evalChoose IsMyTurntoSend st) = true -> (OneProtocolStep st ,st,n) ⇓ (proto_handleIsMyTurnToSend st, st, n).
Proof.
intros; unfold OneProtocolStep; constructor; assumption.
Qed.
Hint Resolve evalSendTurn. 

Theorem evalReceiveTurn : forall st n, (evalChoose IsMyTurntoSend st) = false -> (OneProtocolStep st ,st,n) ⇓ (proto_handleNotMyTurnToSend st, st, n).
Proof. intros; unfold OneProtocolStep; constructor; assumption.
Qed.
Hint Resolve evalReceiveTurn.

Theorem eval_myTurnToSend_queuedRequest : forall st n, (evalChoose QueuedRequestsExist st) = true ->
(evalChoose IsAllGood st) = true ->  
 (proto_handleIsMyTurnToSend st, st, n) ⇓⇓ 
(proto_handleCanSend st, st, n).
Proof. intros. unfold proto_handleIsMyTurnToSend. eapply bigstep_stm_step.
cca. cca.
Qed.
Hint Resolve eval_myTurnToSend_queuedRequest.
Theorem eval_myTurnToSend_NOqueuedRequest : forall st n, (evalChoose QueuedRequestsExist st) = false ->
 (evalChoose IsAllGood st) = true ->  
(proto_handleIsMyTurnToSend st, st, n) ⇓⇓ 
(proto_handleCantSend st, st, n).
Proof. intros; unfold proto_handleIsMyTurnToSend. eapply bigstep_stm_step.
cca. cca.
Qed.
Hint Resolve eval_myTurnToSend_NOqueuedRequest.

Theorem eval_existsNextDesire : forall st n, (evalChoose ExistsNextDesire st) = true -> 
(evalChoose IsAllGood st) = true ->  
(proto_handleCantSend st, st, n) ⇓
 (proto_handleExistsNextDesire st, st, n)
.
Proof. intros; unfold proto_handleIsMyTurnToSend. cca.
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



(*(EndStatement, assign toSendMESSAGE x (state v p), sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) x n)
⇓⇓ (EndStatement, st', n')
*)
(*

*)
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
    | proState _ _ _ pp _ _ _ => pp
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
  (EffectStatement (effect_ReducePrivacyWithRequest t), st, n) ⇓ (Skip, st',n) -> 
  findandMeasureItem (getPrivacy st') d = None.
Proof. intros. inversion H0; subst.
simpl in H2. rewrite H in H2. inversion H2. subst. 
Theorem x : forall d st, findandMeasureItem (getPrivacy (reducePrivacy_w_RequestST d st)) d = None.
intros. destruct st. simpl. destruct p. simpl. auto. Qed. apply x. 
Qed.

Theorem sendWillSend : forall v p n,evalChoose IsMyTurntoSend (state v p) = true -> exists  st' n', 
((OneProtocolStep (state v p) , (state v p), n) ⇓⇓(EndStatement, st', n') 
\/  
(OneProtocolStep (state v p) , (state v p), n) ⇓⇓ (StopStatement, st', n') 
)
 /\  length n + 1 = length n' .
Proof. intros. 
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



 