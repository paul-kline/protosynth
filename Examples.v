
Add LoadPath "/nfs/users/paulkline/Documents/coqs/protosynth".

Add LoadPath "C:\Users\Paul\Documents\coqStuff\protosynth". 
Require Import TrueProtoSynth. 
Module example1.

SearchAbout nat.  
Definition antivirusVersion := descriptor virusCheckerVersionR. 


Definition bankwants := ConsRequestLS (requestItem antivirusVersion (requirement antivirusVersion ( fun (x:(measurementDenote antivirusVersion)) =>  Nat.leb 10 x)) 
)emptyRequestLS. 
Definition bankPrivacy := EmptyPolicy.

Definition Tomwants := emptyRequestLS.
Definition tomPrivacy := @ConsPolicy antivirusVersion (free antivirusVersion) EmptyPolicy.    

Definition bankState := mkAppraiserState bankPrivacy bankwants.
Definition tomState := mkAttesterState tomPrivacy.

Theorem finishes: exists bankState' tomState', 
((OneProtocolStep bankState,bankState), 
 (OneProtocolStep tomState, tomState), nil) 
 ⟱⟱ 
 ((StopStatement, bankState'), (StopStatement, tomState'), nil).
Proof.
eexists. eexists.
eapply dualmultistep_step. apply dualmultistep_id. apply duLeft.
(*bank sends first message. prove it finishes *) 
step. proto.
step. unfold proto_handleIsMyTurnToSend. c. simpl. auto.
step. c. c. simpl. refl.
step. proto.
step. unfold proto_handleCantSend. proto.
step. unfold proto_handleExistsNextDesire. c. c. refl.
step. c. c. refl.
c. c. c.  refl. nono.

eapply dualmultistep_step. apply dualmultistep_id. apply duRight.

(*now tom executes his protocol. *)  
step. proto.
step. unfold proto_handleNotMyTurnToSend. c. c. c. nono.
step. proto.
step. proto.
c. c. c. refl.
(*tom has received, now he must send. *)
  
eapply dualmultistep_step. apply dualmultistep_id.
apply duRight.
step. proto.
step. c. simpl. refl.
step. c. c. refl.
step. proto.
step. c. refl.
step. s. c. c. refl.
step. c. c. refl. nono.
step. c. c. refl.
step. c. c. refl.
c. c. c. refl.

(*now the left side must  receive the measurement *)
eapply dualmultistep_step. apply dualmultistep_id. apply duLeft.
step. proto.
step. c. c. refl. nono.
step. proto.
c. c. c. refl.

(*Now the left side must send the stop. *)
apply dualmultistep_id. eapply duFinishLeftFirst.
step. unfold OneProtocolStep. apply E_ChooseTrue. simpl.
unblock_dep_elim. simpl. simpl_eq. refl.
step. apply E_ChooseFalse.  simpl.  unblock_dep_elim.  simpl.  simpl_eq. refl. 
simpl.  unblock_dep_elim.  simpl.  simpl_eq.      
Tactic Notation "ss" := unblock_dep_elim; simpl; simpl_eq.
c. proto.  refl.

(* now tom must also go to stop. *)
step. proto. unfold proto_handleNotMyTurnToSend. c. c. c. refl.
Qed. 

End example1.

Lemma lemma00 : forall st st' stm x x2 n n', 
(EffectStatement x  >> EndStatement, st, n) ⇓⇓ (SendStatement x2 (getMe st') (notMe (getMe st')) >> stm, st', n') -> False.
Proof. intros. crush.  dep_destruct H. inv H. inv H1. inv H2. inv H1. inv H7. inv H4.
 clear H1. clear H3. clear H2.
 inv H. inv H1. inv H2. inv H1.    
 
  inv H5. inv H1.              
Lemma lemma0 : forall st st' stm x n n', (proto_handleNotMyTurnToSend st, st, n) ⇓⇓ (SendStatement x (getMe st') (notMe (getMe st')) >> stm, st', n') -> False.
Proof. intros.
inv H. inv H1.
inv H2. inv H1.  
 inv H7. inv H4.
 inv H5. inv H4.
inv H11. inv H8. inv H9. inv H8.
       
     
Lemma lemma1 : forall st d n st' n' stm, 
varSubst (variable toSendMESSAGE) st' = Some (constValue d (measure d)) -> 
(OneProtocolStep st, st, n) ⇓⇓ (SendStatement (variable toSendMESSAGE) (getMe st') (notMe (getMe st')) >> stm,st',n') -> 
(OneProtocolStep st, st, n) ⇓ (proto_handleIsMyTurnToSend st, st, n).
Proof. intros. inv H0. inv H2.
inv H3. inv H2.
exact H2.
(* need to prove not true. *)
inv H8. inv H5.
inv H6. inv H5.
inv H12.
inv H9.
inv H10.
inv H9. 
inv H12.
inv H13.
inv H14.
inv H13. inv H13.     
inv H16.
inv H18.
inv H19. inv H18.
inv H25. inv H22.
inv H20. inv H22.
inv H31.
inv H12. inv H26. inv H27.
inv H26. inv H23. inv H30.       inv H5.  inv H29.          

subst.       

exact H
inv ZH2.         
Theorem privacyiscool : forall st n d stm st' n',
(OneProtocolStep st, st, n) ⇓⇓ (SendStatement (const (constValue d (measure d))) (getMe st') (notMe (getMe st')) >> stm,st',n') -> 
snd3 (handleRequest' (getPrivacy st') d) = constValue d (measure d) .
Proof.  intros.
inv H. 
inv H1.

inv H2.  inv H1. clear H2. 

inv H7. inv H2. 
inv H4.  inv H2.
inv H10.  inv H6. 
inv H8.  inv H6.  inv H6. inv H11.   

(*yes *)
inv H14.  inv H13. 
inv H15.  inv H13. 

inv H20.  inv H17. 
inv H18.  inv H17. clear H18.  clear H15. clear H8. clear H4. 

inv H24. inv H4. 
inv H8. inv H4.  simpl  in H4. 
inv H23.  inv H18. 

simpl.  
inv H2.  
inv H2.  inv H3. 
inv H1.  inv H1.

inv H4. 
inv H3. 
inv H1.

inv H2.  
inv H1.  
inv H. 
inv H1. 
subst.   subst.  inv H1.  subst.
inv H2.  subst. 
inv H1.  subst. .
inv H1.  subst. 
inv H7.  subst.  inv H5.  subst.  inv H6.  subst. 
inv H5.  subst. 
inv H5.  subst.
inv H12.  subst.
inv H10. subst. 
inv H11. subst. 
inv H10.  subst.
inv H17.  subst. 
inv H14. subst.

inv H17. subst. 
inv H15. subst. 
inv H14. subst. 
inv H14. subst.   

inv H15. subst.
inv H15.  subst.  
inv H14. subst.
inv H14. subst. 
inv H15. subst.   

inv H21. subst. 
inv H14.  subst. 
inv H15. subst. 
inv H14. subst.

inv H17.  subst. 
inv H18. subst.
inv H19.  subst. 
inv H18. subst. 
inv H18. subst.  
inv H14. subst.
inv H14. subst.
inv H14. subst.    
inv H12.  subst. 
inv H11.  subst. 
inv H4. subst.
inv H11.  subst. 
inv H11.  subst.  
inv H4.  subst. 
inv H17.  subst. 
Theorem X : forall  ppApp ppAtt wants , exists STatt' STapp' n', 
( (OneProtocolStep (mkAppraiserState ppApp wants), mkAppraiserState ppApp wants),  
  (OneProtocolStep (mkAttesterState ppAtt), mkAttesterState ppAtt), nil)  ⟱⟱
((StopStatement, STapp'), (StopStatement, STatt'), n') .
Proof.  intro. induction ppApp; intros.   
eexists. eexists. exists nil.
step.
(*appraiser makes first move*)
eapply duFinishLeftFirst. 
step. proto. unfold proto_handleIsMyTurnToSend.   
proto. 
proto. 
proto.
destruct wants. simpl.
proto. 
proto.  refl.
c.  c.

proto. destruct r. 
step. c.  c.  simpl.   refl.
proto.
simpl. 
proto.  
c.  
proto.  
unfold proto_handleCantSend.  step.
proto.
apply E_ChooseFalse; reflexivity.  c.  simpl.  
proto. 
Ltac proto2 := match goal with 

 end. proto2.  refl.   proto2; [ proto|].   
proto.  proto. .  
 (apply dualmultistep_step) || ((eapply dualmultistep_id) ; [constructor|]).
step. 
eapply dualmultistep_step.   