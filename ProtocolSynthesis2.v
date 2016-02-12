(* 

Class Measurable (A : Set) : Set := {
  description : A ;
  value       : A 
  }. *)
(*   
Print Measurable.
 *)
(* Inductive pcr : Set :=
 | pcrdescription : nat -> pcr
 | pcrvalue       : nat -> pcr.
  *)(* 
Instance PCR : Measurable pcr.
apply Build_Measurable. Abort. *)

Inductive Noun : Set:=
  | VirusChecker
  | PCR.
  
Print Noun.

Require Import String. 
 
Inductive Adjective : Set :=
  | Name : Adjective
  | Hash : Adjective
  | Index : nat -> Adjective
  | Version : Adjective. 

Inductive type : Set :=
  | Nat
  | Bool.
Inductive DescriptionR : Noun -> Adjective -> Set :=
  | pcrM : forall n, DescriptionR PCR (Index n) 
  | virusCheckerName : DescriptionR VirusChecker Name
  | virusCheckerVersion : DescriptionR VirusChecker Version.
    
Check pcrM.
Check DescriptionR.
Check DescriptionR PCR. (* 
Check DescriptionR PCR Index. *)
Check pcrM.    

Definition HashT := nat. 
Definition VersionT := nat. 
Definition measurementType {n} {a}( m : DescriptionR n a) : Set :=
match m with
 | pcrM n => nat
 | virusCheckerName => string
 | virusCheckerVersion => VersionT
end%type.

Check measurementType.
Eval compute in (measurementType (pcrM 4)). 

Open Scope string_scope.
Definition measure {noun} {a} (m : DescriptionR noun a) : measurementType m :=
match m with
 | pcrM n => n * n
 | virusCheckerName => "Hello!!!"
 | virusCheckerVersion => 7
end. 

Inductive request : Set :=
 | nothin : request
 | somethin {no} {a} : DescriptionR no a -> request -> request.
 
Definition myrequest := somethin (pcrM 2) (somethin virusCheckerName nothin).

Print myrequest.  
                
  


  
  

Definition x : pcrM -> Type. 
Inductive Value : type -> Set :=
  | pcrV : nat -> Value . 