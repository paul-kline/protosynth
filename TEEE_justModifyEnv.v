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
Theorem measurement_dec : (forall x y:Measurement, {x = y} + {x <> y}). 
Proof. decide equality.  Defined. 
 
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
 | vMeas : Measurement -> VarID
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
 | Store : VarID -> Result -> Program
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

Definition gen_measure (vid :VarID) (m : Measurement) : Program :=
Calc (measurementTypes m) vid (calcMeasure m).
 
Definition gen_delayedMeasure (vid : VarID) (m : Measurement) (d : Time) : Program := 
  Delay d >> gen_measure vid m. 
  
Inductive Property : Type :=
  | FlowRate : Property
  | FlowRateConsistency : Property
  | BatteryVoltage : Property
  | BatteryChargeLevel : Property
  | BatteryHealth : Property
  | Temperature : Property.


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
 
Fixpoint tmap (A: Set) (ls : list Measurement) : Set  :=
match ls with
 | nil => A
 | cons x xs => (TypesDenote (measurementTypes x)) -> (tmap A xs) 
end. 
Definition notb (b : bool) : bool :=
match b with
 | true => false
 | false => true
end. 

Eval compute in (tmap Program (getNeededMeasurements FlowRate)). 


Inductive MVPair :=
 | mvp (m : Measurement): (TypesDenote (measurementTypes m) ) -> MVPair.
Definition mvpair_getM (mp : MVPair) : Measurement :=
match mp with
 | mvp m x => m
end. 

 
 Check MVPair. 
 Import ListNotations.
 Import List.  

Definition xor (A : Prop) (B: Prop) := (A \/ B) /\ ~(A /\ B).
Check xor.  
Class Environment  :={
  env_assumptions :  list MVPair;  
  env_measurables : list Measurement; 
  env_measure : forall m, In m env_measurables ->  (TypesDenote(measurementTypes m)); 
  exclusivity : forall m : Measurement, 
    xor (In m (map mvpair_getM env_assumptions)) (In m env_measurables)}. 


Definition basicMeasurable (m : Measurement) : bool :=
match m with
 | MotorSpeed => true
 | BatteryVoltage_ => true
 | Temperature_ => true
 | MotorOn => true
 | _ => false
end.
Definition linear := fun m : nat => m. 

Definition basicAssumptions := [mvp MotorInterpolation linear;
                                mvp BriefDischargeTest 1;
                                mvp TubeDiameter 3;
                                mvp mmPerRevolution 2].
Definition basicMeasurables := [MotorSpeed; 
                                BatteryVoltage_;
                                Temperature_;
                                MotorOn]. 

Require Import Omega. 
Theorem basicP :  forall m : Measurement, 

    xor (In m (map mvpair_getM basicAssumptions)) (In m basicMeasurables).
Proof. intros. unfold xor. simpl. destruct m; split; auto.
unfold not.  intros.  destruct H. inversion H.  inversion H1. 
inversion H1.  inversion H2.  inversion H2.  inversion H3.  inversion H3. 
inversion H4. assumption.
Admitted .
Definition basicMeasure {m} (_ : (In m basicMeasurables)) : (TypesDenote(measurementTypes m)). destruct m; simpl in H; simpl. simpl in H.
exact 1. 
exfalso. inversion H. inversion H0.
inversion H0.  inversion H1. inversion H1.  inversion H2.
inversion H2.  inversion H3.  assumption.
exact 2.  
exfalso. inversion H. inversion H0.
inversion H0.  inversion H1. inversion H1.  inversion H2.
inversion H2.  inversion H3.  assumption.
exact 3. 
exfalso. inversion H. inversion H0.
inversion H0.  inversion H1. inversion H1.  inversion H2.
inversion H2.  inversion H3.  assumption. 
exfalso. inversion H. inversion H0.
inversion H0.  inversion H1. inversion H1.  inversion H2.
inversion H2.  inversion H3.  assumption. 
exact true.
Defined. 

Instance basicEnvironmentinstance : Environment :=
{ env_assumptions := basicAssumptions;
  env_measurables := basicMeasurables;
  env_measure := @basicMeasure;
  exclusivity := basicP
}.


Check measure. 

Definition inb := in_dec measurement_dec.
Check inb. 
  
(*
Definition getProgramType (p : Property) (e : Environment): Set :=
( 
tmap Program (filter (getNeededMeasurements p) (compose notb (env_measurable a)))
).*)

Definition get_env_measurables (e : Environment) :=
match e with
 | Build_Environment env_assumptions env_measurables env_measure exclusivity => env_measurables
end. 
Definition get_env_assumptions (e : Environment) :=
match e with
 | Build_Environment env_assumptions env_measurables env_measure exclusivity => env_assumptions
end. 

Theorem not_measuable_imp_assumption : forall m e, ~(In m (get_env_measurables e)) -> In m (map mvpair_getM (get_env_assumptions e)).
Proof.  intro.  intro. destruct e.   unfold not.  intro. simpl.
simpl in H.  
specialize exclusivity0 with m.
unfold xor in exclusivity0. destruct exclusivity0.
unfold not in H1.  destruct H0.  assumption. 
exfalso.  apply H.  assumption.  Qed.

Theorem eq_dec_Measurement : forall x y : Measurement, {x =y} + {x <> y}.
Proof. decide equality. Defined. 
 (*If this is Qed and not Defined, nothing simplifies!! *)
Fixpoint assLookup (m : Measurement) (ls : list MVPair) : option (TypesDenote (measurementTypes m)). refine (
match ls with
 | nil => None
 | cons x ls' => match x with
        | mvp m' v => if eq_dec_Measurement m m' then Some _ else assLookup m ls'
end 
end). 
Proof. subst.  exact v. 
Defined. 

Require Import Coq.Program.Equality. 

Theorem assLookupThm : forall e m, In m (map mvpair_getM (get_env_assumptions e)) -> 
exists v, assLookup m (get_env_assumptions e) = Some v.
Proof.  intros.  destruct e. simpl.  simpl in H.
  specialize exclusivity0 with m. unfold xor in exclusivity0.
  destruct exclusivity0. induction env_assumptions0.
  simpl.  inversion H.
  simpl. destruct a. 
  destruct (eq_dec_Measurement m m0).  subst. 
  simpl.
  exists t. 
  
   simpl_eq.  reflexivity.
  apply IHenv_assumptions0.
  destruct H0.  simpl in H0.
  destruct H0.  exfalso.  apply n.  auto.
  left.  assumption. 
  right.  assumption.
  unfold not.  intros. destruct H2. 
  apply H1.  split. 
  simpl.  right. assumption.  assumption.
  simpl in H.  destruct H.  exfalso. apply n. auto. 
  assumption. 
 Defined.

Definition assumptionLookup (m : Measurement) (e : Environment)  (p : ~(In m (get_env_measurables e))) :
TypesDenote (measurementTypes m). 
Proof. apply not_measuable_imp_assumption in p.
apply assLookupThm in p. 
simpl in p. 
destruct (assLookup m (get_env_assumptions e)) .
exact t.   exfalso.
inversion p. 
inversion H. 
Defined. 

Definition gen_measureE (e : Environment) (m : Measurement)  : Program.
refine ( if inb m (get_env_measurables e) then
     gen_measure (vMeas m) m
      else Store (vMeas m) (@result (measurementTypes m) (assumptionLookup m e _))
)
. assumption. 
Defined.



Fixpoint concat_Program (ls : list Program) : Program :=
match ls with
 | nil => End
 | cons End ls' => concat_Program ls'
 | cons x ls' =>  x >> (concat_Program ls')
end. 

Definition gen_measureAll (e : Environment) (p : Property) :=
concat_Program (map (gen_measureE e) (getNeededMeasurements p)). 

 
Definition gen_flowRateProgram (e : Environment) : Program :=
 gen_measureAll e FlowRate.
 
Eval compute in (gen_flowRateProgram basicEnvironmentinstance). 


match p with
 | FlowRate => _
 | FlowRateConsistency => _
 | BatteryVoltage => _
 | BatteryChargeLevel => _
 | BatteryHealth => _
 | Temperature => _
end

Definition getProgram (p : Property) (e : Environment) : Program :=
match p with
 | FlowRate => _
 | FlowRateConsistency => _
 | BatteryVoltage => _
 | BatteryChargeLevel => _
 | BatteryHealth => _
 | Temperature => _
end. 
 
 
  


 . 