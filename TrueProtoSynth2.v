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
Add LoadPath "/home/paul/Documents/coqs/protosynth".
Add LoadPath "/home/paul/Documents/coqs/protosynth/cpdt/src" as Cpdt. 
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
Require Import ProtoSynthProtocolDataTypes. 
Require Import Coq.Lists.List.
Require  Export TrueProtoSynth.
(*
Require Import Coq.Program.Equality.
Require Import Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Peano_dec.
*)




Check des1. 


Theorem eval1 : forall st v (n: Network) a allg part pp rls unres l,
st = state v (proState a allg part pp rls unres l) -> 
evalChoose IsAllGood st         = true ->
evalChoose IsMyTurntoSend st     = true -> 
evalChoose QueuedRequestsExist st= true ->
evalChoose CanSend st            = true -> exists d  p0,   
 (OneProtocolStep st, st, n) ⇒* (EndStatement,state ((variden 1, constRequest d) :: (toSendMESSAGE, constValue d (measure d)) :: v) (proState a Yes part (rmAllFromPolicy p0 d) rls unres (tail l)) ,sendOnNetwork (getMe st) (notMe (getMe st)) (constValue d (measure d)) n).
Proof.
intros. destruct st. s. dest p. destruct (canSend l0 p0) eqn:hh.  
destruct l0. inv hh. 
destruct (handleRequest' p0 d0) eqn:hhh. destruct p1. destruct c eqn:cc.

eexists. eexists.  proto. proto. proto.  step.  apply E_ChooseTrue. auto.

step. apply E_ChooseTrue.  auto.
step.  s. apply E_Chain. apply E_Compute. auto. s. rewrite hhh.
 refl. 
(*whew*)
step. apply E_Chain. s. apply E_Send. s. auto. nono.
step.  apply E_Chain. apply E_Compute. s. dest l0.  simpl in hh. refl. 
refl. 
step. apply E_Chain.  apply E_Effect. s. refl.
step. apply E_Chain.  apply E_Effect. s. refl.
c. s. apply E_Chain.   apply E_Effect. s.
apply thm_canSendL in hh. simpl in hh. inv hh. 
apply thm_handleRequestL in hhh. subst.
inv H.  refl.

(* next maybe *) 
eexists. eexists.  proto. proto. proto.  step.  apply E_ChooseTrue. auto.

step. apply E_ChooseTrue.  auto.
step.  s. apply E_Chain. apply E_Compute. s.  auto. s. rewrite hhh. sh.
rewrite hhh in hh. rewrite hhh in H3. inv H3. 
step.  apply E_Chain.  apply E_Send.  simpl. refl.
Show Existentials.
Existential 5 := c. subst.  
nono. 

step. apply E_Chain. apply E_Compute. 
simpl. refl. 
step. apply E_Chain. apply E_Effect. simpl. refl.
step. apply E_Chain. apply E_Effect. simpl. refl. 
c. apply E_Chain. subst. sh. rewrite hhh in H3. inv H3. 
sh. rewrite hhh in H3. inv H3. sh. rewrite hh in H3. inv H3. 
Unshelve. auto. auto. 
Defined. 

Theorem eval2 : forall v p n, 
evalChoose IsAllGood (state v p)           = true ->
evalChoose IsMyTurntoSend (state v p)      = true -> 
evalChoose QueuedRequestsExist (state v p) = true ->
evalChoose CanSend (state v p)             = false ->   
(OneProtocolStep (state v p), (state v p), n) ⇒* (StopStatement, setAllGood No  (state v p) , (sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) constStop n)).
Proof. intros. dest p. unfold OneProtocolStep.
step. apply E_ChooseTrue. auto. 
step. unfold proto_handleIsMyTurnToSend.
simpl. apply E_ChooseTrue. auto. 
step. apply E_Chain.
 apply E_Effect. s.  auto. 
 step. apply E_ChooseTrue.  auto.
step. unfold proto_handleCanSend. s.  
apply E_ChooseFalse. auto.
s. 
step. apply E_Chain. apply E_Effect. simpl. refl.
c. simpl. apply E_ChainBad. eapply E_SendStop. auto.
Qed.


Theorem ifwillthenway : forall st, evalChoose ExistsNextDesire st = true ->exists c,  handleCompute compGetNextRequest st = Some c .
    Proof. intros. destruct st. 
    simpl. destruct p.   destruct r. simpl in H.  inv H.
simpl in H. destruct r.  exists (constRequest d). auto. 
    Qed.


(*(EndStatement, mvNextDesire (assign toSendMESSAGE x (state v p)), sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) x n)
*)
Theorem eval3 : forall v p n, 
evalChoose IsAllGood (state v p)           = true ->
evalChoose IsMyTurntoSend (state v p)      = true -> 
evalChoose QueuedRequestsExist (state v p) = false ->
evalChoose ExistsNextDesire (state v p)    = true ->   exists r,
(OneProtocolStep (state v p), (state v p), n) ⇒* (EndStatement, mvNextDesire (assign toSendMESSAGE r (state v p)), (sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) r n)).
Proof. intros. destruct p. destruct r. sh. inv H2. destruct r. unfold OneProtocolStep.
eexists.
step.  apply E_ChooseTrue. auto. 
step. unfold proto_handleIsMyTurnToSend. apply E_ChooseTrue. auto. 
step. apply E_Chain. apply E_Effect. s.  auto.
step. apply E_ChooseFalse.  auto.
step. unfold proto_handleCantSend. apply E_ChooseTrue. auto. 
step. unfold proto_handleExistsNextDesire.  apply E_Chain. apply E_Compute. s.
destruct r. refl. s.
step. chain. apply E_Effect.  s. refl.
step. chain. s.  apply E_Send.  s. refl. nono.
c. chain. s. apply E_Effect. s. destruct a0. refl. 
sh. inv H. sh. inv H. 
Qed.

(*
(StopStatement, state v p, sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) constStop n)*)
Theorem eval4 : forall v p n, 
evalChoose IsAllGood (state v p)           = true ->
evalChoose IsMyTurntoSend (state v p)      = true -> 
evalChoose QueuedRequestsExist (state v p) = false ->
evalChoose ExistsNextDesire (state v p)    = false -> 
(OneProtocolStep (state v p), (state v p), n) ⇒* (StopStatement, state v p, (sendOnNetwork (getMe (state v p)) (notMe (getMe (state v p))) constStop n)).
Proof. intros. unfold OneProtocolStep.
step. apply E_ChooseTrue.  auto. 
step. unfold proto_handleIsMyTurnToSend. apply E_ChooseTrue. auto.
destruct p. 
step.  s. apply E_Chain.  s. apply E_Effect.  s. refl.
step. apply E_ChooseFalse. auto. 
step. unfold proto_handleCantSend.  apply E_ChooseFalse.  auto.
step. unfold proto_handleNoNextDesire.  chain. apply E_Effect. s. refl. 
c. apply E_ChainBad. destruct a0.  s.  sh.  apply E_SendStop.  auto.
sh. inv H. sh. inv H. 
Qed.

Theorem eval5 : forall v p n d c, 
evalChoose IsMyTurntoSend (state v p)      = false -> 
receiveN n (getMe (state v p)) = Some (constValue d c, tail n) -> exists pp',
reduceStateWithMeasurement (constValue d c) (assign receivedMESSAGE (constValue d c) (state v p)) = pp' -> 
(OneProtocolStep (state v p), (state v p), n) ⇒* (EndStatement, (assign receivedMESSAGE (constValue d c) (reduceStateWithMeasurement (constValue d c)(state v p)) ), tail n).
Proof. intros. unfold OneProtocolStep.
 intros. destruct p.  destruct (reduceUnresolved d c r0) eqn:hh.
 destruct a.  sh. inv H. destruct a0. sh.     
eexists. intros.  step. apply E_ChooseFalse.  auto. 
step. unfold proto_handleNotMyTurnToSend. chain. apply E_Receive. s. rewrite H0. auto.
 nono. 
step.  apply E_ChooseTrue. s. auto. 
c.  sh. chain. eapply E_Effect. s. rewrite hh. rewrite hh in H1.  refl.
sh.  

eexists. intros.  step. apply E_ChooseFalse.  auto. 
step. unfold proto_handleNotMyTurnToSend. chain. apply E_Receive. s. rewrite H0. auto.
 nono. 
step.  apply E_ChooseTrue. s. auto. 
c.  sh. chain. eapply E_Effect. s. rewrite hh. rewrite hh in H1.  refl.
sh.

eexists. intros.  step. apply E_ChooseFalse.  auto. 
step. unfold proto_handleNotMyTurnToSend. chain. apply E_Receive. s. rewrite H0. auto.
 nono. 
step.  apply E_ChooseTrue. s. auto. 
c.  sh. chain. eapply E_Effect. s. rewrite hh. rewrite hh in H1.  refl.
sh.  

eexists. intros.  step. apply E_ChooseFalse.  auto. 
step. unfold proto_handleNotMyTurnToSend. chain. apply E_Receive. s. rewrite H0. auto.
 nono. 
step.  apply E_ChooseTrue. s. auto. 
c.  sh. chain. eapply E_Effect. s. rewrite hh. rewrite hh in H1.  refl.

Unshelve.  exact (state v (proState AReceive Yes p p0 r r0 l) ) . 
exact (state v (proState AReceive Yes p p0 r r0 l) ) . 
exact (state v (proState AReceive Yes p p0 r r0 l) ) . 
exact (state v (proState AReceive Yes p p0 r r0 l) ) . 
Qed. 

Theorem eval6 : forall v p n r, 
evalChoose IsMyTurntoSend (state v p)      = false -> 
receiveN n (getMe (state v p)) = Some (constRequest r, tail n) -> 
(OneProtocolStep (state v p), (state v p), n) ⇒* (EndStatement, (storeRequest r (assign receivedMESSAGE (constRequest r) (state v p))), tail n).
Proof. intros. unfold OneProtocolStep.
step. apply E_ChooseFalse.  auto. 
step. unfold proto_handleNotMyTurnToSend.  chain. apply E_Receive. rewrite H0. refl. nono. 
step. apply E_ChooseFalse.  s. destruct p. auto. 
step. apply E_ChooseTrue. s. destruct p. auto.
destruct p. 
c. chain. apply E_Effect. s.  refl.
Qed.

Theorem eval7 : forall v p n, 
evalChoose IsMyTurntoSend (state v p)      = false -> 
receiveN n (getMe (state v p)) = Some (constStop, tail n) -> 
(OneProtocolStep (state v p), (state v p), n) ⇒* (StopStatement,  (assign receivedMESSAGE constStop (state v p)), tail n).
Proof. intros. unfold OneProtocolStep.
step.  apply E_ChooseFalse. auto.
c. unfold proto_handleNotMyTurnToSend. apply E_ChainBad. apply E_ReceiveStop. auto. 
Qed.

Theorem eval8 : forall v p n, 
evalChoose IsMyTurntoSend (state v p)      = false -> 
receiveN n (getMe (state v p)) = None -> 
(OneProtocolStep (state v p), (state v p), n) ⇒* (Wait >> (proto_handleNotMyTurnToSend (state v p)),   (state v p), n).
Proof. intros. unfold OneProtocolStep. 
 intros.
step. apply E_ChooseFalse. auto.
c. apply E_ChainWait.  apply E_ReceiveWait. auto.
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
 | dualmultistep_step : forall ds1 ds1' ds2 ds2', 
    ds1 ⟱  ds1' ->
    ds2 ⟱  ds2' ->
    DualMultiStep ds1 ds2'.
Notation "x ⟱* y" := (DualMultiStep x y) (at level 60).
Theorem thm_DualMultiStepOneProtocolStep : forall initReqs ppApp ppAtt, exists stL stR, 
((OneProtocolStep (mkAppraiserState ppApp initReqs), mkAppraiserState ppApp initReqs),  
 (OneProtocolStep (mkAttesterState ppAtt), mkAttesterState ppAtt), nil ) 
 ⟱* ((StopStatement, stL),(StopStatement, stR), nil).
 intros. eexists. eexists. Check eval1.
 unfold mkAttesterState. unfold mkAppraiserState. unfold mkState.  sh.
 remember (state nil
      (proState ASend Yes APPRAISER ppApp initReqs emptyRequestLS nil)) as stL.
 remember (state nil
      (proState AReceive Yes ATTESTER ppAtt emptyRequestLS emptyRequestLS nil)) as stR.
destruct (evalChoose IsAllGood stL) eqn:allgood.
Check eval1.
 assert (evalChoose IsMyTurntoSend stL = true). rewrite HeqstL. s.  auto.
  Check eval1.
destruct (evalChoose QueuedRequestsExist stL) eqn:quedReq.
Check eval1. 
destruct (evalChoose CanSend stL) eqn:cansend.
eapply dualmultistep_step.
c. specialize eval1; intros.  rewrite HeqstL.  eapply eval1.  auto. 
simpl. 
eapply duLeft. 
specialize eval1. intros. specialize H0 with stL.   
c. 
Theorem onlyEffect_effects : forall (stm stm': Statement) (st st': State) (n n' : Network),
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
Hint Resolve onlyEffect_effects.

Theorem receiveAlwaysFinishes : forall vars prst n m n', evalChoose IsMyTurntoSend (state vars prst) = false -> 
 receiveN n (getMe (state vars prst)) = Some (m, n') -> 
 m <> constStop ->  exists prst',
 (OneProtocolStep (state vars prst), (state vars prst), n) ⇒* (EndStatement, (state ((receivedMESSAGE,m)::vars) prst'), n').
Proof. intros. destruct m, prst. destruct (reduceUnresolved d m r0) eqn:unres. eexists. 
eapply multistep_step. c. unfold OneProtocolStep.
proto. step. unfold proto_handleNotMyTurnToSend. c. c. apply H0. auto.
step.  proto.
c. c. c. simpl. rewrite unres.  reflexivity.

eexists.
eapply multistep_step. c. unfold OneProtocolStep.
proto. step. unfold proto_handleNotMyTurnToSend. c. c. apply H0. auto.
step. proto.
c. c. c. simpl. rewrite unres.   reflexivity.

eexists.
eapply multistep_step. c. unfold OneProtocolStep.
proto. step. unfold proto_handleNotMyTurnToSend. c. c. apply H0. auto.
step. proto. simpl.
step. proto. c. c. c. reflexivity.
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
unfold OneProtocolStep.
eapply dualmultistep_step.
induction stR, stL.
rewrite H.  rewrite H0. subst. inv H.  inv H0.

eapply dualmultistep_step. 
 sh. 
unfold OneProtocolStep. destruct H. 
destruct (evalChoose IsAllGood H) eqn:allgood.
evalChoose IsMyTurntoSend st     = true -> 
evalChoose QueuedRequestsExist st= true ->
evalChoose CanSend st            = true -> 
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



 