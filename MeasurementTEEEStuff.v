
Inductive Property : Type :=
  | FlowRate : Property
  | FlowRateConsistency : Property
  | BatteryVoltage : Property
  | BatteryChargeLevel : Property
  | BatteryHealth : Property
  | Temperature : Property.

Inductive Measurment : Type := 
 | MotorSpeed
 | BatteryVoltage_
 | BriefDischargeTest
 | Temperature_
 | TubeDiameter. 

Require Import Coq.Lists.ListSet. 

Notation "x ∈ x'" := (set_mem x x') (at level 60).


Definition PropertyDenote (p : Property) : set Measurment.
refine (match p with
 | FlowRate => _ 
 | FlowRateConsistency => _
 | BatteryVoltage => _
 | BatteryChargeLevel => _
 | BatteryHealth => (set_add _ BatteryVoltage_ (empty_set _))
 | Temperature => _
end). 

  (*How can I measure on demand how the pump functions on a low battery *)
  
  
  
  can I stop the pump? what pressure does it take? how strong is it?