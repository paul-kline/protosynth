
Inductive Noun : Set:=
  | VirusChecker
  | PCR.
  
Create HintDb eq_dec_db. 
Theorem eq_dec_noun : forall n1 n2 : Noun, {n1 = n2} + {n1 <> n2}.
Proof. intros.   destruct n1, n2; 
  try (left;reflexivity); right; unfold not; intros H; inversion H.
Defined.

Hint Resolve eq_dec_noun : eq_dec_db. 
(*Require Import String.*) 
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec. 
Inductive Adjective : Set :=
  | Name : Adjective
  | Hash : Adjective
  | Index : nat -> Adjective
  | Version : Adjective.

Ltac rec_eq :=
 match goal with
    | [ x : ?T, y : ?T |- _ ] => 
       (match T with
        | nat => generalize nat_eq_eqdec
        | bool => generalize bool_eqdec
        | unit => generalize unit_eqdec
       end) ; 
       intros X; destruct X with x y as [| paul];
       try (left; inversion e; subst; reflexivity);
       try (right; unfold complement in paul; unfold not; 
            intros Hpaul; apply paul; inversion Hpaul; reflexivity)
    end.



Theorem eq_dec_adjective : forall a1 a2 : Adjective,
                    {a1 = a2} + {a1 <> a2}.
Proof. decide equality; rec_eq.
Defined. 
Hint Resolve eq_dec_adjective : eq_dec_db. 
Require Import Coq.Program.Equality.
Inductive DescriptionR : Noun -> Adjective -> Set :=
  | pcrMR : forall n, DescriptionR PCR (Index n)
  | virusCheckerNameR : DescriptionR VirusChecker Name
  | virusCheckerVersionR : DescriptionR VirusChecker Version.
  
Theorem eq_dec_DescriptionR1 : 
forall n : Noun,
forall a : Adjective,
forall x y : DescriptionR n a,
x = y.
Proof. intros;
induction x; dependent induction y;
( reflexivity).
Defined. 

Inductive Description : Set :=
  | descriptor {n : Noun} {a : Adjective} : DescriptionR n a -> Description.


Theorem eq_dec_Description : 
forall d1 d2 : Description,
{d1 = d2} + {d1 <> d2}. 
Proof. intros. destruct d1, d2.   
specialize eq_dec_adjective with a a0. intros. destruct H.
 specialize eq_dec_noun with n n0. intros.
destruct H. left. subst. specialize eq_dec_DescriptionR1 with n0 a0 d0 d.
intros. subst. reflexivity.
right. unfold not. intros. inversion H. contradiction.
right. unfold not. intros. inversion H. contradiction.
Defined. 
Hint Resolve eq_dec_Description : eq_dec_db.
Hint Resolve eq_dec_DescriptionR1 : eq_dec_db.  

Add LoadPath "/users/paulkline/Documents/coqs/dependent-crypto".
Add LoadPath "/users/paulkline/Documents/coqs/cpdt/src".
Add LoadPath "C:\Users\Paul\Documents\coqs\dependent-crypto".
Add LoadPath "C:\Users\Paul\Documents\coqs\cpdt\src". 
Require Import MyShortHand.

Definition measurementDenote (d: Description) :=
match d with
 | descriptor r => match r with
    | pcrMR n => nat
    | virusCheckerNameR => nat
    | virusCheckerVersionR => bool
end

end.


Inductive Message : Set :=
| Sendable_Measurement (d: Description) : (measurementDenote d) -> Message
| RequestS : Description -> Message
| StopMessage : Message.
Theorem eq_dec_bool : forall b c : bool, 
{b = c} + {b <> c}.
decide equality.
Defined. 


Require Import Coq.Program.Equality.
Require Import Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Peano_dec.
 
Theorem sendable_measurment_inversion : 
forall d : Description, forall n n1 : (measurementDenote d), 
@Sendable_Measurement d n = @Sendable_Measurement d n1 -> n = n1.
Proof. intros.
inversion H. apply inj_pair2_eq_dec. apply eq_dec_Description. Print existT.   apply H1.
Qed.

(*
Theorem eq_dec_Message : forall x y : Message,
  { x = y} + {x <> y}. Proof. intros. *)
Theorem eq_dec_Message : forall x y : Message,
  { x = y} + {x <> y}.
Proof. intros. destruct x, y. specialize eq_dec_Description with d d0; intros.
destruct H. subst. specialize sendable_measurment_inversion with d0 m0 m.
intros.  
destruct d0. 
destruct n,a.
destruct d.
    simpl in m0, m;
specialize eq_nat_dec with m m0; intros;
destruct H0 as [eq |neq]; subst; ( (left; reflexivity) +
right; unfold not; intros; apply neq; apply symmetry in H0;
apply H in H0; rewrite H0; reflexivity). 
simpl. cbn. simpl in H. simpl in m0. simpl in m.
destruct eq_nat_dec with m0 m. left. subst. refl.
right. unfold not; intros. symmetry in H0. apply H in H0. contradiction.

simpl in m0. simpl in m.
destruct eq_dec_bool with m0 m. left. subst. refl.
right. unfold not; intros. symmetry in H0. apply H in H0. contradiction.
subst. simpl in m.  
destruct d eqn:b. 
Admitted.

Inductive Requirement (d : Description) :=
| requirement : ( (measurementDenote d) -> bool) -> Requirement d.

Check requirement.
Definition  des1 := (descriptor (pcrMR 1)). 
Eval compute in (measurementDenote des1).
Definition req1 : (Requirement des1 ).
Search bool. 
apply requirement. simpl. exact ((fun (x : nat) => Nat.leb x 7)).
Defined.
Definition req2 := 
 requirement (des1) ((fun (x : nat) => Nat.leb x 7)).
 
Inductive Rule (mything : Description) :=  
| rule  {your : Description} : (Requirement your) -> Rule mything
| free : Rule mything
| never : Rule mything
| multiReqAnd : Rule mything ->Rule mything -> Rule mything
| multiReqOr : Rule mything -> Rule mything -> Rule mything.   


Inductive PrivacyPolicy :=
| EmptyPolicy : PrivacyPolicy
| ConsPolicy {d :Description}: 
    Rule d -> 
    PrivacyPolicy -> PrivacyPolicy. 
Check req1.

Definition myRule1 := rule (des1) (requirement (descriptor (pcrMR 2))
 (fun x : nat => Nat.leb x 9)).
Check myRule1.
Check ConsPolicy.
Print myRule1. 
Definition myPrivacyPolicy := ConsPolicy myRule1 EmptyPolicy.
 
 


Definition myrequirement1 := fun (x : nat) => (x > 7).

Inductive Session :=
 | Send : Message -> Session -> Session
 | Receive : (Message -> Session) -> Session
 | Branch : bool -> Session -> Session -> Session
 | Stop : Session
 .

Inductive Action : Set :=
 | ASend : Action
 | AReceive : Action.

 Theorem eq_dec_Action : forall x y : Action,
 {x = y} + {x <>y }.
 Proof. decide equality. Defined.
 
 Require Import Coq.Lists.List.
 
 (* placeholder measurement function. need this to exist *) 
 Definition measure (d: Description) : measurementDenote d.
 destruct d. destruct d. simpl. exact n.
 simpl. exact 0.
 simpl. exact true. Defined.
 
Inductive RequestItem : Set :=
 | requestItem (d : Description) : (Requirement d) -> RequestItem.
 Theorem eq_dec_RequestItem : forall x y : RequestItem,
 {x = y} + {x <> y}. Proof. intros. 
 Admitted.   
Inductive RequestLS : Set :=
 | emptyRequestLS : RequestLS
 | ConsRequestLS : RequestItem -> RequestLS -> RequestLS.
 
Fixpoint reduceUnresolved (d : Description) (v : measurementDenote d)
(ls : RequestLS) : option RequestLS. refine match ls with
 | emptyRequestLS => Some emptyRequestLS
 | ConsRequestLS r x0 => match r with
      | requestItem dr reqment => if eq_dec_Description dr d then
          match reqment with
            | requirement _ f => match f _ with
               | true => Some x0
               | false => None (* give up *)
              end
          end
        else
          match reduceUnresolved d v x0 with 
            | Some some => Some (ConsRequestLS r some)
            | None => None
          end
     end
 end. rewrite <- e in v. exact v. Defined. 
 
Inductive Role : Set :=
 | Appraiser
 | Attester. 
Theorem eq_dec_Role: forall x y : Role, {x = y} + {x <> y}. 
Proof. decide equality. Defined.

Definition freeRequirement (d : Description): Requirement d:= 
 requirement d (fun _ => true).
Definition neverRequirement (d : Description): Requirement d:= 
 requirement d (fun _ => false).
Check neverRequirement.
 
 
 (* note that the rule is removed from the privacy policy. This is to prevent measurement deadlock
 situations. Everything not expressly in the privacy policy is rejected. Therefore, you can't ask
 for the same thing twice. *)
 
Fixpoint handleRequest (pp : PrivacyPolicy) (d : Description) : 
(PrivacyPolicy * Message * RequestItem):=
 match pp with
 | EmptyPolicy => (EmptyPolicy, StopMessage, requestItem d (neverRequirement d))  (*by default, do not give away*)
 | @ConsPolicy dp rule_d pp' => if (eq_dec_Description dp d) 
    then
      match rule_d with
       | @rule _ your reqrment => (pp', RequestS your, requestItem your reqrment)
       | free _ => (pp', Sendable_Measurement d (measure d), requestItem d (freeRequirement d) )
       | never _ => (pp', StopMessage, requestItem d (neverRequirement d)) (*don't matter *)
       | multiReqAnd _ rule1 morerules => (pp', StopMessage, requestItem d (neverRequirement d)) (* TODO *)
       | multiReqOr _ rule1 morerules => (pp', StopMessage, requestItem d (neverRequirement d)) (* TODO *)
      end
    else
     match handleRequest pp' d with
       | (ppres,messres,reqRes) => (@ConsPolicy dp rule_d ppres,messres,reqRes)
     end
 end. 
 

Fixpoint getProtocol (n : nat) (a: Action) (myPriv : PrivacyPolicy) 
 (toRequest : RequestLS) (unresolved : RequestLS): Session :=
match n with
| O => Stop
| S n' =>
 match a with
 | ASend => (match toRequest with
     | emptyRequestLS => Send StopMessage Stop 
     | ConsRequestLS reqItem reqls' => (match reqItem with
         | requestItem d reqment => Send (RequestS d) 
            (getProtocol n' AReceive myPriv reqls' 
               (ConsRequestLS (requestItem d reqment) unresolved) )
         end)
     end)

 | AReceive => Receive (fun m => match m with
             | Sendable_Measurement d v => (match reduceUnresolved d v unresolved with
                 | Some newUnresolvedState => getProtocol n' ASend myPriv toRequest newUnresolvedState
                 | None => Send StopMessage Stop (*fails to meet my reqs I give up *)
                 end) 
             | RequestS d => (match handleRequest myPriv d with 
                 | (_, StopMessage,_) => Send StopMessage Stop
                 | (newpp,mess,reqItem) => Send mess 
                     (getProtocol n' AReceive newpp emptyRequestLS (ConsRequestLS reqItem unresolved) )
                 end)
             | StopMessage => Stop
             end)
 end
 end. 

Check (Receive _). 
Inductive IsValid : Session -> Session -> Prop :=
 | both_stop : IsValid Stop Stop
 | lr_stop : IsValid (Send StopMessage Stop) Stop
 | rl_stop : IsValid Stop (Send StopMessage Stop)
 | lr_send {x} {y} {m} {f}: IsValid x y -> (f m = y) -> IsValid (Send m x) (Receive f) 
 | rl_send {x} {y} {m} {f}: IsValid x y -> (f m = x) -> IsValid (Receive f) (Send m y). 
 
Hint Constructors IsValid. 
Example example1 : IsValid 
(Send StopMessage Stop) 
(Receive (fun p => match p with
   | Sendable_Measurement d x => Send StopMessage Stop
   | RequestS x => Send StopMessage Stop
   | StopMessage => Stop
end)).
Proof. simpl. intros. eauto. Qed. (*  apply lr_stop. reflexivity. Qed. *)     
 
Example example2 : IsValid 
(Receive (fun p => match p with
   | Sendable_Measurement d x => Send StopMessage Stop
   | RequestS x => Send StopMessage Stop
   | StopMessage => Stop
end))
(Send StopMessage Stop).
Proof. simpl. intros. eauto. Qed. (*   apply rl_stop. reflexivity. Qed. *)


Example example3 : IsValid 
(Send (RequestS (descriptor (pcrMR 1))) 
 (Receive (fun p => match p with
   | Sendable_Measurement d x => Send StopMessage Stop
   | RequestS x => Send StopMessage Stop
   | StopMessage => Stop
end)))

(Receive (fun p => (Send StopMessage Stop))).
Proof. intros. cbn.  simpl. Print lr_send. 
apply @lr_send with (Send StopMessage Stop).
apply @rl_send with (Stop). auto.
auto.
auto.         Qed.  (*  specialize example1. intros. specialize example2; intros.
apply @lr_send with (Send StopMessage Stop) . assumption.  reflexivity. Qed.
*)
Example example4 : IsValid 
(Receive (fun p => (Send StopMessage Stop)))

(Send (RequestS (descriptor (pcrMR 1))) 
 (Receive (fun p => match p with
   | Sendable_Measurement d x => Send StopMessage Stop
   | RequestS x => Send StopMessage Stop
   | StopMessage => Stop
end)))

.
Proof. apply @rl_send with (Send StopMessage Stop).
apply @lr_send with Stop.
auto. auto. auto. Qed. 

Definition lenientPolicy := ConsPolicy (free (descriptor (pcrMR 1))) 
(ConsPolicy (free (descriptor (pcrMR 2))) EmptyPolicy). 

Definition lenientishPolicy := ConsPolicy (rule (descriptor (pcrMR 1) ) (requirement (descriptor (pcrMR 1)) (fun x :nat => beq_nat x 1))) 
(ConsPolicy (rule (descriptor (pcrMR 2)) (requirement (descriptor (pcrMR 2)) (fun x :nat => beq_nat x 2)) ) EmptyPolicy).
Check getProtocol.
Definition thingIWant1 := requestItem (descriptor (pcrMR 1)) 
  (requirement (descriptor (pcrMR 1)) (fun x :nat => beq_nat x 1)) .
Definition thingIWant2 := requestItem (descriptor (pcrMR 2)) 
  (requirement (descriptor (pcrMR 2)) (fun x :nat => beq_nat x 2)) .
  (*types must match :D ) *)
Definition thingsIwant := ConsRequestLS thingIWant1 emptyRequestLS.

Definition attesterproto1 := getProtocol 5 AReceive lenientPolicy emptyRequestLS emptyRequestLS.
Definition appraiserProto1 := getProtocol 5 ASend EmptyPolicy thingsIwant emptyRequestLS.

Definition attesterproto2 := getProtocol 5 AReceive EmptyPolicy emptyRequestLS emptyRequestLS.
Definition appraiserProto2 := getProtocol 5 ASend EmptyPolicy thingsIwant emptyRequestLS.

Definition attesterproto3 := getProtocol 5 AReceive lenientishPolicy emptyRequestLS emptyRequestLS.
Definition appraiserProto3 := getProtocol 5 ASend lenientPolicy thingsIwant emptyRequestLS.


Eval compute in appraiserProto1.


Definition reduce (m : Message) (sess : Session) :=
match sess with
 | Send x x0 => sess
 | Receive f => Receive (fun _ => f m) 
 | Branch x x0 x1 => sess
 | Stop => Stop
end. 


Theorem subValid : forall m x f, IsValid (Send m x) (Receive f) -> IsValid x (f m).
Proof. intros. inversion H. subst. exact H3.
Qed. 
Hint Resolve subValid.
Theorem subValid2 : forall m x f, IsValid (Receive f) (Send m x) -> IsValid (f m) x.
Proof. intros. inversion H. subst.
subst. exact H3.
Qed. 
Hint Resolve subValid2.

Theorem reducingIsOkay : forall f m x, IsValid (Send m x) (Receive f) <-> 
  IsValid (Send m x) (reduce m (Receive f)).
Proof. split.  intros. simpl. apply subValid in H. apply @lr_send  with ( f m). exact H.
reflexivity.
intros. simpl. simpl in H. apply @lr_send with (f m). inversion H. subst. exact H3.
reflexivity.           
 Qed.

Theorem reducingIsOkay2 : forall f m x, IsValid (Receive f) (Send m x) <-> 
  IsValid (reduce m (Receive f)) (Send m x) .
Proof. split.  intros. simpl. apply subValid2 in H. apply @rl_send  with ( f m). exact H.
reflexivity.
intros. simpl. simpl in H. apply @rl_send with (f m). inversion H. subst. exact H3. 
reflexivity.
 Qed.

Definition getNext (m : Message) (sess : Session) : Session :=
match sess with
 | Send x x0 => x0
 | Receive x => x m 
 | Branch x x0 x1 => x1
 | Stop => Stop
end.

Inductive TwoSessions :=
 | twoSessions : Session -> Session -> TwoSessions. 
Definition smallStep dos : TwoSessions:=
 match dos with 
  | twoSessions (Send m s1') (Receive f) => twoSessions s1' (f m) 
  | twoSessions (Receive f) (Send m s2') => twoSessions (f m) s2'
  | _ => dos
 end.
 
 Eval cbn in getNext (Sendable_Measurement 
    (descriptor (pcrMR 1)) 1) (getNext _ appraiserProto1). 
  
Definition x := Eval cbn in  smallStep (smallStep (smallStep (twoSessions appraiserProto1 attesterproto1))).
Print x .

Fixpoint bigStep (s1 : Session) (s2 : Session) : option (Session*Session) :=
 match (s1,s2) with 
  | ((Send m s1'), (Receive f)) => bigStep s1' (f m) 
  | ((Receive f), (Send m s2')) => bigStep (f m) s2'
  | (Stop, Stop) => Some (Stop, Stop)
  | _ => None
 end.
 
Eval cbn in (bigStep appraiserProto1 attesterproto1).
Eval compute in appraiserProto1.
 
 Import Coq.Program.Equality. 
Example eijeifjfij : (bigStep appraiserProto1 attesterproto1) = Some (Stop,Stop).
Proof. unfold appraiserProto1. unfold attesterproto1. cbn. unblock_goal. simpl. cbn.
cbn. eauto. simpl_eq. reflexivity.
Qed.

Eval compute in smallStep (smallStep (smallStep (twoSessions appraiserProto2 attesterproto2))). 
Example eefffees2 : (bigStep appraiserProto2 attesterproto2) = Some (Stop,Stop).
Proof.  unfold appraiserProto2. unfold attesterproto2. simpl.
reflexivity. Qed. 


Theorem IsValid_IsValid : forall x y, IsValid x y -> IsValid y x.
Proof. intros. induction H; auto || eauto.
Qed. 

Theorem bigStep_implies_IsValid : forall x y : Session, (bigStep x y) = Some (Stop,Stop) -> 
 IsValid x y. Proof. intro. induction x0. simpl. destruct y eqn:what. simpl.
 intros.
 inversion H.
 intros. apply IHx0 in H. eauto.
 intros. inversion H.
 intros. inversion H.
 intros. eauto.
    destruct y. eauto.
    inversion H0.
    inversion H0.
    simpl in H0. inversion H0.
    intros. simpl in H. inversion H.
    intros. simpl in H.
    destruct y; (try inversion H).
    auto.
    Qed.
    
Example example5 : IsValid appraiserProto1 attesterproto1.
Proof. intros. apply bigStep_implies_IsValid.
  cbn. unblock_goal. simpl_eq. reflexivity.
  Qed.
  
  Check getProtocol.
  
Ltac proto := match goal with 
  | [  |- IsValid (Send ?M ?X) (Receive ?F)] => 
           apply @lr_send with (F M)
  | [  |- IsValid (Receive ?F) (Send ?M ?X)] => 
           apply @rl_send with (F M)
  | [  |- IsValid Stop Stop ] => 
           apply  both_stop
  | [  |- IsValid Stop  (Send StopMessage Stop)] => 
           apply lr_stop
  | [  |- IsValid (Send StopMessage Stop) Stop] => 
           apply rl_stop
  
  end.
  
  Eval compute in bigStep appraiserProto3 attesterproto3. 
Example efijefijeg3 : IsValid appraiserProto3 attesterproto3.
unfold appraiserProto3. unfold attesterproto3. simpl. proto. 
unblock_goal. simpl_eq.  
proto. simpl_eq. proto. simpl_eq. proto. auto. auto.
simpl_eq. refl. simpl_eq. auto. simpl_eq. reflexivity.
Qed.

Ltac proto_simpler := match goal with
  | [ |- IsValid ?X ?Y] => progress (simpl_eq || proto || auto)
  | [ |- ?X = ?Y] => auto
  end.
  Example testa : IsValid appraiserProto3 attesterproto3.
  Proof. unfold appraiserProto3. unfold attesterproto3. repeat proto_simpler.
  Qed.

  
  
Theorem WillStop_Receive : forall n a pp rls un f, (getProtocol n a pp rls un) = Receive f ->
  f StopMessage = Stop. 
Proof. intros. destruct n, a, pp, rls, un; ( simpl in H; inversion H).  
try (destruct r; inversion H1).  destruct r. inversion H1. destruct r0. inversion H1.
destruct r0. inversion H1.
repeat reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Qed.

Theorem willReceive : forall n pp rls un, exists f, (getProtocol (S n) AReceive pp rls un) = Receive f. 
Proof. intros. induction n. simpl. exists (fun m : Message =>
     match m with
     | Sendable_Measurement d v =>
         match reduceUnresolved d v un with
         | Some _ => Stop
         | None => Send StopMessage Stop
         end
     | RequestS d =>
         let (p, _) := handleRequest pp d in
         let (_, mess) := p in
         match mess with
         | Sendable_Measurement _ _ => Send mess Stop
         | RequestS _ => Send mess Stop
         | StopMessage => Send StopMessage Stop
         end
     | StopMessage => Stop
     end). simpl. eauto. simpl. eauto. Qed.

Theorem IsValid_WillStoprl : 
 forall n pp rls un, IsValid (getProtocol (S n) AReceive pp rls un) (Send StopMessage Stop).
 intros. intros. proto_simpler. proto_simpler. auto. auto. Qed.
 
Theorem IsValid_WillStoplr : 
 forall n pp rls un, IsValid (Send StopMessage Stop) (getProtocol (S n) AReceive pp rls un).
  intros. proto_simpler. proto_simpler. auto. auto. Qed.

Theorem WillStop_Send : forall n a pp rls un r, (getProtocol n a pp rls un) = Send StopMessage r ->
  r = Stop. 
Proof. intros. destruct n, a, pp, rls, un; ( simpl in H; inversion H); auto.
 destruct r0. simpl in H1. inversion H1.
 destruct r0. inversion H1. 
 destruct r1. inversion H1.
 destruct r1. inversion H1.
 Qed.
Theorem wellduh_eq_dec_Adjective :
 forall x, exists p : x =x, eq_dec_adjective  x x= left p.
 intros. case_eq (eq_dec_adjective x0 x0). intros. exists e. reflexivity.
 intros. assert (x0 = x0). refl. contradiction. Qed.
 
 Theorem wellduh_eq_dec_Noun :
forall x, exists p : x =x, eq_dec_noun  x x= left p.
 intros. case_eq (eq_dec_noun x0 x0). intros. exists e. reflexivity.
 intros. assert (x0 = x0). refl. contradiction. Qed.
 
Theorem wellduh_eq_dec_Description : 
forall x, exists p : x = x, eq_dec_Description x x = left p.
 intros. case_eq (eq_dec_Description x0 x0). intros. exists e. reflexivity.
 intros. assert (x0 = x0). refl. contradiction. Qed.
 
 
Theorem IguessThatsOkay : forall m, 
IsValid Stop ((Send m) Stop).
Admitted.
 
Theorem IsValid_inc : forall n pp1 pp2 rls1 rls2 un1 un2,
  IsValid (getProtocol (n) ASend pp1 rls1 un1) (getProtocol ( n) AReceive pp2 rls2 un2) ->
  IsValid (getProtocol (S n) ASend pp1 rls1 un1) (getProtocol (S n ) AReceive pp2 rls2 un2).
  Proof. intro. induction n. simpl. intros.  destruct rls1.  proto_simpler.
  auto. auto. destruct r. proto_simpler. destruct (handleRequest pp2 d).
  destruct p. destruct m . apply IguessThatsOkay. apply IguessThatsOkay. auto.
  destruct (handleRequest pp2 d). destruct p.
  destruct m. auto. auto. auto. intros.  simpl. proto_simpler.
  destruct rls1. proto_simpler.  
  proto_simpler. refl. destruct r. simpl.                   proto_simpler.
  destruct (handleRequest pp2 d). destruct p. destruct m.
   proto_simpler. destruct (eq_dec_Description d d0). simpl. destruct r. subst.   simpl_eq.
   destruct (b m). Admitted.
   
  Theorem allGood : forall n pp1 pp2 rls1 un1 un2,
 IsValid (getProtocol (S n) ASend pp1 rls1 un1) (getProtocol (S n) AReceive pp2 emptyRequestLS un2).
 Proof. intro. induction n. simpl. intros. destruct rls1. proto_simpler. auto. auto.
 destruct r. proto_simpler. destruct (handleRequest pp2 d).
 destruct p. destruct m. apply IguessThatsOkay. apply IguessThatsOkay. auto.
 destruct (handleRequest pp2 d). destruct p.
 destruct m. refl. refl. refl.          
 specialize IsValid_inc. intros. apply H. apply IHn.
 Qed.