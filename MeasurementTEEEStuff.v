Add LoadPath "/nfs/users/paulkline/Documents/coqs/protosynth/cpdt/src".
Add LoadPath "~/Documents/coqs/protosynth/cpdt/src".

 
(* 
  direct/abstract desires called properites 
*)
Inductive Property : Type :=
  | FlowRate : Property
  | FlowRateConsistency : Property
  | BatteryVoltage : Property
  | BatteryChargeLevel : Property
  | BatteryHealth : Property
  | Temperature : Property.

(*
       The difference between Properties and Measurments is that no further 
  derivation is needed. These are directly measurable from the environment.
  In combination, these can give more meaningful measurments.
 
      For example, If one would like to know the flow rate
 over a certain period of time, this can be derived from the repeated
 application of measuring the motor speed. However every measurment result
 contains a list of assumptions. In this example we must assume:
   a. The motor speeds up/ slows down linearly between discrete measurments.
      (or some specified function, linear is easiest)
   b. The diameter of the tube is known.
   c. back EMF -> speed.
   d. Components measuring back EMF are correct.

 Then it is useful, to not only get back the result of querying a property, 
  but the list of assumptions made to obtain that value. These assumptions 
  are not yet implemented.
*)

(* Instead of Measurements, let's have Measurments, which can be measurments, or
assumptions depending on the environment. As the environment gets stronger, we 
can turn assumptions into measurments. *)

Inductive InterpolationMethod :Set :=
 | Linear
 | Quadratic.


Inductive Measurement : Type := 
 | MotorSpeed
 | MotorInterpolation
 | BatteryVoltage_
 | BriefDischargeTest
 | Temperature_
 | TubeDiameter
 | MotorOn.
 

Check Prop -> Prop -> Prop.


Module MeasurementProgramModule.

Definition measurementDenote (m : Measurement) :=
match m with
 | MotorSpeed => nat
 | BatteryVoltage_ => nat
 | BriefDischargeTest => nat
 | Temperature_ => nat
 | TubeDiameter => nat
 | MotorOn => bool
 | MotorInterpolation => InterpolationMethod
end.

Class Environment A :={
  measurable : A -> Measurement -> bool; 
  measure (a : A) (m: Measurement) : (measurable a m) = true ->  (measurementDenote m) }.


Inductive BasicEnvironment :=
 basicEnvironment.
Definition basicMeasurable (m : Measurement) : bool :=
match m with
 | MotorSpeed => true
 | BatteryVoltage_ => true
 | Temperature_ => true
 | MotorOn => true
 | _ => false
end.
Definition basicMeasure {m} (p : (basicMeasurable m) = true ) : 
(measurementDenote m).  destruct m. 
exact 1. inversion p.  exact 1. inversion p.  exact 1. inversion p.  exact true. 
Defined.

Instance basicEnvironmentinstance : Environment BasicEnvironment :=
{ measurable := fun _ => basicMeasurable;
  measure := fun _ _ p => basicMeasure p
}.

Check measure. 

Inductive Const : Set := 
 | const_dep (m : Measurement) : (measurementDenote m) -> Const
 | const_nat : nat -> Const
 | const_bool : bool -> Const.
 
Inductive VarID : Set :=
 | varid : nat -> VarID
 | returnVar : VarID.
  
Inductive Term : Set :=
 | t_const : Const -> Term
 | t_var : VarID -> Term.

Inductive Cond : Set :=
 | WaitOver : Cond.
  
Inductive MeasurmentProgram : Set :=
 | mp_measure : VarID -> Measurement -> MeasurmentProgram
 | mp_delay : nat -> MeasurmentProgram
 | mp_loop  : Cond -> MeasurmentProgram -> MeasurmentProgram
 | mp_Mult : VarID -> Term -> Term -> MeasurmentProgram
 | mp_Div  : VarID -> Term -> Term -> MeasurmentProgram
 | mp_Add  : VarID -> Term -> Term -> MeasurmentProgram
 | mp_Subtract : VarID -> Term -> Term -> MeasurmentProgram
 | mp_Power : VarID -> Term -> Term -> MeasurmentProgram
 | mp_Chain : MeasurmentProgram -> MeasurmentProgram -> MeasurmentProgram. 
Notation "x '>>' y" := (mp_Chain x y)  (at level 60, right associativity).

Inductive MUnits : Set :=
 | metersCubedPerSecond. 
 

(* dummy state *)
Inductive State := 
 state : nat -> State.
 Check nat -> Prop. 

(* right now, programs are simply the measurment of the requested value.
  
  
  *)
Definition synthMeasurementProgram (m : Measurement) : MeasurmentProgram :=
match m with
 | MotorSpeed => mp_measure returnVar MotorSpeed
 | BatteryVoltage_ => mp_measure returnVar BatteryVoltage_
 | BriefDischargeTest => mp_measure returnVar BriefDischargeTest
 | Temperature_ => mp_measure returnVar Temperature_
 | TubeDiameter => mp_measure returnVar TubeDiameter 
 | MotorOn => mp_measure returnVar MotorOn
 | MotorInterpolation => mp_measure returnVar MotorInterpolation
end.

(* 
Thinking of a MeasurmentProgram as a function that returns the value of the
requested measurement, evaluation returns a value (Const).

Currently only 1 evaluation rule. That is that evaluation of a measurment
   statement returns the measured value. 
   
We may also wish to include the Units of measurments and ensure measuring/
conversion of properties is correct. Yes, but this is a rabbithole of difficulty. Perhaps a 'lite' version. 
*)

Inductive eval : MeasurmentProgram -> State -> Environment -> Const -> Prop:=
 | evalm: forall m var st env, eval (mp_measure var m) st env 
  (const_dep m (measure m env)). 
 

 

End MeasurementProgramModule. 


Require Import Coq.Lists.ListSet. 

Notation "x ∈ x'" := (set_mem x x') (at level 60).


Inductive BaseUnit : Set :=
 | Ampere
 | Candela
 | Kelvin
 | Kilogram
 | Metre
 | Mole
 | Second.

Inductive OtherUnit : Set :=
 | Inch
 | Centimeter.
