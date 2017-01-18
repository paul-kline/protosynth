(* Inductive BaseUnit : Set :=
 | Ampere
 | Candela
 | Kelvin
 | Kilogram
 | Metre
 | Mole
 | Second.
*)
 
Inductive Length :=
 | Inch
 | Meter
 | MilliMeter
 | Centimeter.

Inductive Time :=
 | MilliSecond
 | Second
 | Minute
 | Hour
 | Day.

Inductive Temperature :=
 | Fahrenheit
 | Celcius
 | Kelvin.

Inductive Weight :=
 | Pound
 | Gram
 | Kilogram
 | Stone.

Inductive Unit :=
 | unit_temp : Temperature -> Unit
 | unit_length : Length -> Unit
 | unit_time : Time -> Unit
 | unit_weight : Weight -> Unit
 .
Inductive DerivedUnit : Set :=
 | unit : forall u : Unit,  DerivedUnit   
 | div  : forall x y : DerivedUnit, DerivedUnit
 | mult : forall x y : DerivedUnit, DerivedUnit
 | pow  : forall x : DerivedUnit, forall n : nat, DerivedUnit. 
Notation "x ⋅ y" := (mult x y) (at level 60).
Notation "x // y" := (div x y) (at level 60).
Notation " x ^^ y" := (pow x y) (at level 60).
Check pow.

Theorem eq_dec_DerivedUnit : forall x y : DerivedUnit, {x = y} + {x <> y}.
Proof. intros; repeat decide equality.
Qed.

Inductive Value : DerivedUnit -> Set :=
 value : forall (n : nat), forall (d : DerivedUnit), Value d. 
Definition val {d} (v : Value d) : nat :=
match v with
 | value n d => n
end. 

Inductive Opp {d} : Value d -> Set :=
 | addopp : forall x y : (Value d), Opp (value ( (val x) + (val y))d  )
 | subopp : forall x y : (Value d), Opp (value ( (val x) - (val y))d  )
 | divopp : forall d1 d2 : DerivedUnit, (d1 // d2) = d ->
          forall x : (Value d1), forall (y : Value d2), Opp (value ( Nat.div (val x) (val y)) d)
 | multopp : forall d1 d2 : DerivedUnit, (mult d1  d2) = d ->
          forall x : (Value d1), forall (y : Value d2), Opp (value ( Nat.mul (val x) (val y)) d)
          .

Fixpoint removeUnit (d : DerivedUnit) (d2 : DerivedUnit) : DerivedUnit :=
match d2 with
 | unit u => d2 
 | div x y => d2
 | mult x y => if eq_dec_DerivedUnit x d then y else mult x (removeUnit d y)
 | pow x n => d2
end. 
 

Inductive Area : DerivedUnit -> Set :=
 | area : forall l : Length, Area ((unit (unit_length l)) ^^ 2).
 Check Area.

Definition Areaa := forall l : Length, ((unit (unit_length l)) ^^ 2).  
(* volume *)
Definition Liter := 1 //

Notation