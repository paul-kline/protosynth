Add LoadPath "/users/paulkline/Documents/coqs/protosynth". 
Add LoadPath "/home/paul/Documents/coqs/protosynth/cpdt/src" as Cpdt. 
Require Import MyShortHand.
Require Import ProtoSynthDataTypes.

Inductive VarID :=
 | receivedMESSAGE : VarID
 | toSendMESSAGE : VarID
 | variden : nat -> VarID.
Theorem eq_dec_VarID : equality VarID. 
crush_equal. 
Defined.
Hint Resolve eq_dec_VarID : eq_dec_db. 

Inductive Const :=
 | constValue (d: Description) : (measurementDenote d) -> Const 
 | constRequest : Description -> Const
 | constStop : Const.
Theorem eq_dec_Const : equality Const.
intro_equals. 
destruct x,y.
dep_destruct_equality nm.
destruct nm.  subst.
dep_destruct_equality nm2.
destruct d0; try crush_equal.
destruct d; crush_equal.
crush_equal. 
crush_equal. 
crush_equal.
decidable. 
decidable.
crush_equal.  
decidable.
decidable. 
decidable. 
decidable.
Defined. 
Hint Resolve eq_dec_Const : eq_dec_db. 

Inductive Term :=
 | variable : VarID -> Term
 | const : Const -> Term.
Theorem eq_dec_Term : equality Term. 
crush_equal. 
Defined. 
Hint Resolve eq_dec_Term : eq_dec_db. 

Inductive Condition :=
 | IsMyTurntoSend : Condition
 | QueuedRequestsExist : Condition
 | ExistsNextDesire : Condition
 | CanSend :  Condition
 | IsSend :  Condition
 | IsMeasurement : Term -> Condition
 | IsRequest : Term -> Condition
 | IsStop : Term -> Condition
 | IsAllGood : Condition.
Theorem eq_dec_Condition : equality Condition. 
crush_equal. 
Defined. 
Hint Resolve eq_dec_Condition : eq_dec_Condition. 

Inductive AllGood :=
 | Yes
 | No
 | Unset.
Theorem eq_dec_AllGood : equality AllGood. 
crush_equal. 
Defined. 
Hint Resolve eq_dec_AllGood : eq_dec_db. 

Inductive Computation := 
 | compGetMessageToSend
 | compGetNextRequest
 | compGetfstQueue.
Theorem eq_dec_Computation : equality Computation. 
crush_equal. 
Defined. 
Hint Resolve eq_dec_Computation : eq_dec_db. 

Inductive Effect :=
 | effect_StoreRequest : Term -> Effect
 | effect_ReduceStatewithMeasurement : Term -> Effect
 | effect_ReducePrivacyWithRequest : Term -> Effect
 | effect_MvFirstDesire :  Effect
 | effect_rmFstQueued : Effect
 | effect_cp_ppUnresolved : Term -> Effect
 | effect_setAllGood : AllGood -> Effect.
Theorem eq_dec_Effect : equality Effect. 
crush_equal. 
Defined. 
Hint Resolve eq_dec_Effect : eq_dec_db. 
Inductive Participant :=
 | ATTESTER
 | APPRAISER.
Theorem eq_dec_Participant : equality Participant. 
crush_equal. 
Defined. 
Hint Resolve eq_dec_Participant : eq_dec_db. 
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
 | Wait : Statement.
Theorem eq_dec_Statement : equality Statement. 
crush_equal. 
Defined. 
Hint Resolve eq_dec_Statement : eq_dec_Statement. 
Notation "'IFS' x 'THEN' y 'ELSE' z" := (Choose x y z)(at level 80, right associativity). 
Notation "x '>>' y" := (Chain x y)  (at level 60, right associativity).

Definition VarState := list (VarID*Const).
Theorem eq_dec_VarState : equality VarState. 
crush_equal. 
Defined.
Hint Resolve eq_dec_VarState : eq_dec_db. 
 
Inductive ProState :=
 (*  action <who am I?> privacyPol <things I want to ask for!> <Things I've asked for and am waiting for a response> tosend *)
 | proState : Action -> AllGood -> Participant ->  PrivacyPolicy -> RequestLS -> RequestLS -> list Description
      -> ProState.
Theorem eq_dec_ProState : equality ProState.
crush_equal. 
Defined. 
Hint Resolve eq_dec_ProState : eq_dec_db. 
      
Inductive State :=
 state : VarState -> ProState -> State.
Theorem eq_dec_State : equality State.
crush_equal. 
Defined. 
Hint Resolve eq_dec_State : eq_dec_db. 

Inductive NetworkMessage :=
 networkMessage : Participant -> Participant -> Const -> NetworkMessage.
Theorem eq_dec_NetworkMessage : equality NetworkMessage.
crush_equal. 
Defined. 
Hint Resolve eq_dec_NetworkMessage : eq_dec_db. 
 
Definition Network := list NetworkMessage.
Theorem eq_dec_Network : equality Network. 
crush_equal. 
Defined. 
Hint Resolve eq_dec_Network : eq_dec_db. 

Definition mkState (a : Action) (p : Participant) (pp : PrivacyPolicy) (rls : RequestLS) : State:=
 state nil (proState a Yes p pp rls emptyRequestLS nil).
 
Definition mkAppraiserState (pp : PrivacyPolicy) (rls : RequestLS) : State :=
 mkState ASend APPRAISER pp rls.
Definition mkAttesterState (pp : PrivacyPolicy) : State := 
 mkState AReceive ATTESTER pp emptyRequestLS.