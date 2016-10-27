
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
step. c. c. refl. nono.
c. c.
eapply dualmultistep_step. apply dualmultistep_id. apply duRight.

(*now tom executes his protocol. *)  
step. proto.
step. unfold proto_handleNotMyTurnToSend. c. c. c. nono.
step. proto.
step. proto.
step. c. c. refl.
c. c. 
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
step. c. c. refl.
c. c.

(*now the left side must  receive the measurement *)
eapply dualmultistep_step. apply dualmultistep_id. apply duLeft.
step. proto.
step. c. c. refl. nono.
step. proto.
step. c. c. refl.
c. c.
(*Now the left side must send the stop. *)
apply dualmultistep_id. eapply duFinishLeftFirst.
step. unfold OneProtocolStep. apply E_ChooseTrue. simpl.
unblock_dep_elim. simpl. simpl_eq. refl.    

 SearchAbout block. simpl_eqs. unblock goal.  auto.  refl.   simpl.   apply E_Ch proto.   c. simpl.  refl.   proto.     
simpl. 
step.     step.   c.      
simpl. 

  simpl. 

step. proto.
step. c. c. simpl.  refl.    proto.    
 .  c.  
apply dualmultistep_step. 
step.     proto.         
c.                
         proto.       proto.     
End example1.  