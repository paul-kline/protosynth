Inductive Types :=
 | rpms
 | meterscubedpersecond
 | volts
 | degreesC
 | function
 | millimeters
 | boolstate
 .
 

Inductive Measurement : Type := 
 | MotorSpeed
 | MotorInterpolation
 | BatteryVoltage_
 | BriefDischargeTest
 | Temperature_
 | TubeDiameter
 | MotorOn.

Inductive InterpolationMethod :Set :=
 | Linear
 | Quadratic.

Definition measurementTypes (m : Measurement) : Types :=
match m with
 | MotorSpeed => rpms
 | BatteryVoltage_ => volts
 | BriefDischargeTest => volts
 | Temperature_ => degreesC
 | TubeDiameter => millimeters
 | MotorOn => boolstate
 | MotorInterpolation => function
end.

Definition TypesDenote (t : Types) :=
match t with
 | rpms => nat
 | meterscubedpersecond => nat
 | volts => nat
 | degreesC => nat
 | function => nat -> nat
 | millimeters => nat
 | boolstate => bool
end. 
Eval compute in (TypesDenote function).

 
Definition measure (m : Measurement) : (TypesDenote (measurementTypes m)).
Admitted.   


Definition Time := nat. 
(* The calculation language *)
(*  gives me trouble later when trying to create inductive eval. 
Inductive Result (t : Types)  : Set:=
 | result : (TypesDenote t) -> Result t.

*)

Inductive Result : Set :=
 | result {t} : (TypesDenote t) -> Result. 


  (*
Definition resType ( r : Result) : Types :=
match r with
 | result t x => t
end.

Theorem resTypeIsCorrect : forall (r : Result), forall t, forall x, 
  r = (result t x) -> resType r = t. 
Proof. intros. rewrite H. simpl. reflexivity. 
Qed.
*)



Inductive Calculation :=
 | calcMeasure : Measurement -> Calculation 
 | calcAdd : Calculation -> Calculation -> Calculation.
 
Inductive TypedCalculation : Calculation -> Types ->  Prop := 
 | TcalcMeasure : forall m, TypedCalculation (calcMeasure m) (measurementTypes m)
 | TcalcAdd     : forall c1 c2 t1 t2, 
     TypedCalculation c1 t1 -> 
     TypedCalculation c2 t2 -> t1 = t2 -> TypedCalculation (calcAdd c1 c2) t1. 


Definition typeOf (r : Result) := 
match r with
 | @result t x => t
end.
Check typeOf.  

(* dep typed version *)
(*
Definition addResults {t1 t2} (r1 r2 : (Result t)) (p : r1 = r2) : Result t.
destruct t; (destruct r1 as [t1]); (destruct r2 as [t2]); simpl in t1; simpl in t2.
exact (result rpms (t1 + t2)).
exact (result meterscubedpersecond (t1 + t2)).
exact (result volts (t1 + t2)).
exact (result degreesC (t1 + t2)).
exact (result function (fun x => t1 (t2 x))).
exact (result millimeters (t1 + t2)).
exact (result boolstate (andb t1 t2)).
Defined.
*)
Definition addResult (r1 r2 : Result) {p : ((typeOf r1) = (typeOf r2))} : Result :=
 match (r1,r2) with 
  | (result v1, result v2) => r1
 end. 
 
 (* don't need. hopefully. *)
 (*
Inductive WResult : Set :=
 | wr {t} : Result t -> WResult.

Check @wr. 

Definition resT {t} (x : (Result t)) := t.
Definition getT (r : WResult) := 
match r with
 | wr x => (resT x)
end.

Definition unwrap (x : WResult) : (Result (getT x)).
destruct x. simpl. exact r.
Defined.

Check unwrap.
*)
Inductive EvalCalculation : Calculation -> Result -> Prop :=
 | evalcMeasure (m : Measurement) : EvalCalculation (calcMeasure m) 
      (@result (measurementTypes m) (measure m))
 | evalcAdd_same :
      forall c1 c2 : Calculation, forall r1 r2, 
      EvalCalculation c1 r1 ->
      EvalCalculation c2 r2 ->
      forall p : ((typeOf r1) = (typeOf r2)),
      EvalCalculation (calcAdd c1 c2) ( (@addResult r1 r2 p)). 

Inductive VarID :=
 | vnat : nat -> VarID
 | vReturn. 
Require Import Coq.Classes.EquivDec.
Theorem eq_dec_VarId : forall x y : VarID, {x = y} + {x <> y}.
Proof. repeat decide equality. 
Defined.
  
Inductive TypedVar : Types -> Set  :=
 | VarRPMs : VarID -> nat -> TypedVar rpms.  


Inductive Var :=
 | var : forall t : Types,  TypedVar t -> Var. 

Inductive Program :=
 | Calc : Types -> VarID ->  Calculation -> Program 
 | Delay : nat -> Program
 | Chain : Program -> Program -> Program
 | End.


Definition VarState := list (VarID*Result).
 
Fixpoint lookup (vid : VarID) (vs : VarState) : option Result :=
 match vs with 
  | nil => None
  | cons (vid',r) vs' => if  eq_dec_VarId vid vid' then Some r else 
      lookup vid vs'
 end. 


Inductive State :=
 | state : Time -> VarState -> State.
Definition getVS (s : State) : VarState :=
match s with
 | state t vs => vs
end. 

Definition gettime (s : State) : Time :=
match s with
 | state t vs => t
end.

Inductive evalProgram : (Program * State) -> State -> Prop:=
 | eCalc : forall c r id s, 
             EvalCalculation c r -> evalProgram ((Calc (typeOf r) id c),s)
                                      (state (gettime s) (cons (id,r) (getVS s))) 
 | eDelay : forall n s, evalProgram ((Delay n),s) (state ((gettime s) + n) (getVS s))
 | eChain : forall p1 p2 s1 s1' s2', 
     evalProgram (p1,s1) s1' ->
     evalProgram (p2, s1') s2' -> 
     evalProgram (Chain p1 p2, s1) s2'. 


 . 