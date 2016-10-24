Add LoadPath "/users/paulkline/Documents/coqs/protosynth". 
Require Import MyShortHand.
Require Import ProtoSynthDataTypes.

Inductive VarID :=
 | receivedMESSAGE : VarID
 | toSendMESSAGE : VarID
 | variden : nat -> VarID.

Inductive Const :=
 | constValue (d: Description) : (measurementDenote d) -> Const 
 | constRequest : Description -> Const
 | constStop : Const
 | constNULL : Const
 | constMeasurementPlaceHolder : Const.

Inductive Term :=
 | variable : VarID -> Term
 | const : Const -> Term.

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

Inductive AllGood :=
 | Yes
 | No
 | Unset.

Inductive Computation := 
 | compGetMessageToSend
 | compGetNextRequest
 | compGetfstQueue.

Inductive Effect :=
 | effect_StoreRequest : Term -> Effect
 | effect_ReduceStatewithMeasurement : Term -> Effect
 | effect_ReducePrivacyWithRequest : Term -> Effect
 | effect_MvFirstDesire :  Effect
 | effect_rmFstQueued : Effect
 | effect_cp_ppUnresolved : Term -> Effect
 | effect_setAllGood : AllGood -> Effect.

Inductive Participant :=
 | ATTESTER
 | APPRAISER.

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

Notation "'IFS' x 'THEN' y 'ELSE' z" := (Choose x y z)(at level 80, right associativity). 
Notation "x '>>' y" := (Chain x y)  (at level 60, right associativity).

Definition VarState := list (VarID*Const).
 
Inductive ProState :=
 (*  action <who am I?> privacyPol <things I want to ask for!> <Things I've asked for and am waiting for a response> tosend *)
 | proState : Action -> AllGood -> Participant ->  PrivacyPolicy -> RequestLS -> RequestLS -> list Description
      -> ProState.
      
Inductive State :=
 state : VarState -> ProState -> State.

Inductive NetworkMessage :=
 networkMessage : Participant -> Participant -> Const -> NetworkMessage. 
Definition Network := list NetworkMessage.