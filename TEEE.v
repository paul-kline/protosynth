Inductive Types :=
 | rpms
 | meterscubedpersecond
 | volts
 | degreesC
 | function
 | millimeters
 | mmPerRevolutionT
 | boolstate
 .
 

Inductive Measurement : Type := 
 | MotorSpeed
 | MotorInterpolation
 | BatteryVoltage_
 | BriefDischargeTest
 | Temperature_
 | TubeDiameter
 | mmPerRevolution
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
 | mmPerRevolution => mmPerRevolutionT
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
 | mmPerRevolutionT => nat
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

Definition VarF := VarID -> option Result. 
Definition emptyVars : VarF := fun _ => None.
  
 (*
Fixpoint lookup (vid : VarID) (vs : VarState) : option Result :=
 match vs with 
  | nil => None
  | cons (vid',r) vs' => if  eq_dec_VarId vid vid' then Some r else 
      lookup vid vs'
 end. 
*)

Inductive State :=
 | state : Time -> VarF -> State.
 
Definition getVF (s : State) : VarF :=
match s with
 | state t vs => vs
end. 

Definition gettime (s : State) : Time :=
match s with
 | state t vs => t
end.
Definition varSet (id : VarID) (r : Result) (vf : VarF) : VarF :=
 fun qID : VarID => if eq_dec_VarId qID id then Some r else (vf qID).  

Inductive evalProgram : (Program * State) -> State -> Prop:=
 | eCalc : forall c r id s, 
             EvalCalculation c r -> evalProgram ((Calc (typeOf r) id c),s)
              (state (gettime s) (varSet id r (getVF s))) 
 | eDelay : forall n s, evalProgram ((Delay n),s) (state ((gettime s) + n) (getVF s))
 | eChain : forall p1 p2 s1 s1' s2', 
     evalProgram (p1,s1) s1' ->
     evalProgram (p2, s1') s2' -> 
     evalProgram (Chain p1 p2, s1) s2'. 
     
Notation "x '>>' y" := (Chain x y)  (at level 60, right associativity).
Definition delayedMeasure (vid : VarID) (m : Measurement) (d : Time) : Program := 
  Delay d >>
  Calc (measurementTypes m) vid (calcMeasure m).
  
Inductive Property : Type :=
  | FlowRate : Property
  | FlowRateConsistency : Property
  | BatteryVoltage : Property
  | BatteryChargeLevel : Property
  | BatteryHealth : Property
  | Temperature : Property.


Class Environment A :={
  env_measurable : A -> Measurement -> bool; 
  env_measure (a : A) (m: Measurement) : (env_measurable a m) = true ->  (TypesDenote(measurementTypes m)) }.


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
(TypesDenote (measurementTypes m)).  destruct m. 
exact 1. inversion p.  exact 1. inversion p.  exact 1. inversion p.
inversion p.   exact true. 
Defined.

Instance basicEnvironmentinstance : Environment BasicEnvironment :=
{ env_measurable := fun _ => basicMeasurable;
  env_measure := fun _ _ p => basicMeasure p
}.

Check measure. 

(*
https://coq.inria.fr/library/Coq.Lists.List.html
*)
Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..) (compat "8.4") : list_scope.
End ListNotations.

Import ListNotations.
   
Definition getNeededMeasurements (p : Property) : list Measurement:=
match p with
 | FlowRate => [ TubeDiameter ; MotorSpeed ; mmPerRevolution ]
 | FlowRateConsistency => [ TubeDiameter ; MotorSpeed ; mmPerRevolution ]
 | BatteryVoltage => [ BatteryVoltage_ ]
 | BatteryChargeLevel => [ BatteryVoltage_ ]
 | BatteryHealth => [ BatteryVoltage_ ]
 | Temperature => [Temperature_]
end.

Fixpoint map {A} {B} (ls : list A) (f : A -> B) : list B :=
match ls with
 | nil => nil
 | cons x xs => cons (f x) (map xs f)
end.
Fixpoint filter {A} (ls : list A) (f : A -> bool) : list A :=
match ls with
 | nil => nil
 | cons x xs => if (f x) then cons x (filter xs f) else filter xs f
end.

Definition compose {A} {B} {C} (fbc : B -> C) (fab : A ->B) : (A -> C) :=
 fun x : A => fbc (fab x). 
 Check compose. 
Check nat. 
Fixpoint tmap (ls : list Measurement) : Set  :=
match ls with
 | nil => Program
 | cons x xs => (TypesDenote (measurementTypes x)) -> (tmap xs) 
end. 
Definition notb (b : bool) : bool :=
match b with
 | true => false
 | false => true
end. 

Eval compute in (tmap (getNeededMeasurements FlowRate)). 

Eval compute in ((compose notb (env_measurable BasicEnvironment ))). 
Definition getProgramType {A} (p : Property) (e : Environment A) : Set. refine
( 
tmap (filter (getNeededMeasurements p) (compose notb (env_measurable _)))
).   



Definition getProgram {A} (p : Property) (e : Environment A) : (getProgramType p e). :=
match p with
 | FlowRate => _
 | FlowRateConsistency => _
 | BatteryVoltage => _
 | BatteryChargeLevel => _
 | BatteryHealth => _
 | Temperature => _
end
 
 
  


 . 