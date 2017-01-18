Inductive Types :=
 | rpms
 | meterscubedpersecond
 | volts
 | degreesC
 | function
 | millimeters
 | boolstate
 . 
 
Inductive VarIdentifier :=
 | vnat : nat -> VarIdentifier
 | vReturn. 
 
Inductive TypedVar : Types -> Set  :=
 | VarRPMs : VarIdentifier -> nat -> TypedVar rpms.  


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
Inductive Calculation :=
 | calcValue (m : Measurement) : TypesDenote (measurementTypes m) -> Calculation
 | calcMeasure : Measurement -> Calculation 
 | calcAdd : Calculation -> Calculation.

Definition add : Calcul

Inductive EvalCalculation : Calculation -> Prop :=
 | evalcMeasure (m : Measurement) : EvalCalculation (calcMeasure m) ->
     EvalCalculation (calcValue m (measure m)). 
 | evalcAdd (c1 c2 : Calculation, : Calculation -> EvalCalculation  Calculation. 
Inductive Var :=
 | var : forall t : Types,  TypedVar t -> Var. 

Inductive Program :=
 | Calc : Var ->  Calculation -> Program
 | Measure (m : Measurement) :
     TypedVar (measurementTypes m) -> Program
 | Delay : nat -> Program
 | Chain : Program -> Program -> Program.
 
Inductive evalProgram :=
 | eCalc
 