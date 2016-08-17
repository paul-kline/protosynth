(* Goals:
1. Generate protocols from:
     a. A list of what one would like to know about the other
     b. One's own privacy policy

2. The protocol generator should:
     a. Ask for all items listed in (1)a.
     b. Never violate the privacy policy in (1)b.
     c. Never generate protocols that don't "match up."
        i.e. all protocols are valid and will execute properly.
     d. Always terminate.
*)

(* The first step is to define what it is for which we would like to ask. Hence "nouns". *)

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

 (* Now we define what it is we would like to know about these nouns. *)
Inductive Attribute : Set :=
  | Name : Attribute
  | Hash : Attribute
  | Index : nat -> Attribute
  | Version : Attribute.

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



Theorem eq_dec_attribute : forall a1 a2 : Attribute,
                    {a1 = a2} + {a1 <> a2}.
Proof. decide equality; rec_eq.
Defined. 
Hint Resolve eq_dec_attribute : eq_dec_db. 
Require Import Coq.Program.Equality.

(*We only want to disallow nonsensical combinations, like a (PCR, version),
 hence this relation. *)
Inductive DescriptionR : Noun -> Attribute -> Set :=
  | pcrMR : forall n, DescriptionR PCR (Index n)
  | virusCheckerNameR : DescriptionR VirusChecker Name
  | virusCheckerVersionR : DescriptionR VirusChecker Version.
  
Theorem eq_dec_DescriptionR1 : 
forall n : Noun,
forall a : Attribute,
forall x y : DescriptionR n a,
x = y.
Proof. intros;
induction x; dependent induction y;
( reflexivity).
Defined. 

(* This 'extra step' is done simply so that comparison between descriptors
is 'easy.'It is much more involved to be able to compare indexed types. *)

Inductive Description : Set :=
  | descriptor {n : Noun} {a : Attribute} : DescriptionR n a -> Description.


Theorem eq_dec_Description : 
forall d1 d2 : Description,
{d1 = d2} + {d1 <> d2}. 
Proof. intros. destruct d1, d2.   
specialize eq_dec_attribute with a a0. intros. destruct H.
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

(*This defines what the type of measuring these things should be. *)

Definition measurementDenote (d: Description) :=
match d with
 | descriptor r => match r with
    | pcrMR n => nat
    | virusCheckerNameR => nat
    | virusCheckerVersionR => bool
end

end.


(*Let us add to our building blocks by defining what a message can be.
  In it's simplest form, a message can only be a request (RequestS) or a response to a request.
  It turns out a response to a request can take the form of any of the 3 defined messages. 
   1. You can comply with the request and send a "Sendable_Measurement."
   2. You can conditionally comply with the request by countering with another request, depending on its
      result. 
   3. You can refuse all together with a StopMessage.
  A StopMessage is also used to indicate good termination, i.e. I'm done.
  
  
  We must "lock in" what it is that we have measured. We do this in
  the type of Sendable_Measurement.*)

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



Theorem lemma1 : forall d : Description, forall m1 m2 : (measurementDenote d), {m1 = m2} + {m1 <> m2}.
Proof. intros. destruct d. destruct d; simpl in m1; simpl in m2; (apply nat_eq_eqdec) || (apply bool_eqdec).
Qed.
(*
Theorem eq_dec_Message : forall x y : Message,
  { x = y} + {x <> y}. Proof. intros. *)
  
  Ltac not_eq := let x := fresh "beats" in (let y := fresh "beats" in  ((try right); unfold not; intros x; inversion x as [y];
     (try (apply inj_pair2_eq_dec in y); auto with eq_dec_db)  )).
Theorem eq_dec_Message : forall x y : Message,
  { x = y} + {x <> y}.   
Proof. intros. destruct x. destruct y.   destruct (eq_dec_Description d d0). subst. destruct (lemma1 d0 m m0); subst.
left. refl. right. not_eq. not_eq. not_eq. not_eq.
destruct y. not_eq.
destruct (eq_dec_Description d d0). subst. left. refl.
not_eq. not_eq. destruct y. not_eq. not_eq. left; refl.
Defined. 


(* Here we begin specificiation of requirements. So not only do I want a particular measurment,
   but I want it to be certain values. *) 

Inductive Requirement (d : Description) :=
| requirement : ( (measurementDenote d) -> bool) -> Requirement d.

Check requirement.

(*Examples *)
Definition  des1 := (descriptor (pcrMR 1)). 
Eval compute in (measurementDenote des1).
Definition req1 : (Requirement des1 ).
Search bool. 
apply requirement. simpl. exact ((fun (x : nat) => Nat.leb x 7)).
Defined.
Definition req2 := 
 requirement (des1) ((fun (x : nat) => Nat.leb x 7)).
 
 (* This begins the defining of what a privacy policy is. First we define a rule.
    A rule regulates the release of a measurement. We could decide to release information if
    some counter condition holds; we could release it for free; we could explicitly never release it; 
    or some combination of and-ing and or-ing rules.
    Note that at this point we've allowed for nonsensical release rules like, "never release or release for free",
     "release for free and never release".
    
    
    NOTE: If we can't request something twice, what if duplicate occurs in rule req?
          todo: keep all received measurements and check those first for the value *) 
Inductive Rule (mything : Description) :=  
| rule  {your : Description} : (Requirement your) -> Rule mything
| free : Rule mything
| never : Rule mything
| multiReqAnd : Rule mything ->Rule mything -> Rule mything
| multiReqOr : Rule mything -> Rule mything -> Rule mything.   


(* simply a list of rules. *)
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

(* Here is what a session is: We either send something
   and then another Session, or receive a message and 
   produce another session. A Branch is shown here, but never used.*)
Inductive Session :=
 | Send : Message -> Session -> Session
 | Receive : (Message -> Session) -> Session
 | Branch : bool -> Session -> Session -> Session
 | Stop : Session
 .

(* This helps with protocol generation. *)
Inductive Action : Set :=
 | ASend : Action
 | AReceive : Action.

 Theorem eq_dec_Action : forall x y : Action,
 {x = y} + {x <>y }.
 Proof. decide equality. Defined.
 
 Require Import Coq.Lists.List.
 
 (* placeholder measurement function. need this to exist *) 
 Definition measure (d: Description) : measurementDenote d.
 Proof. destruct d. destruct d. simpl. exact n.
 simpl. exact 0.
 simpl. exact true. 
 Defined.
 
 (*A RequestItem is used to compose a list of the items and requirements upon those items in an attestation *)
Inductive RequestItem : Set :=
 | requestItem (d : Description) : (Requirement d) -> RequestItem.
 Theorem eq_dec_RequestItem : forall x y : RequestItem,
 {x = y} + {x <> y}. Proof. intros. destruct x. destruct y. destruct (eq_dec_Description d d0). subst.
 destruct r0. (*Need function equality. Do I need equality on this? *)      
 Admitted.   
Inductive RequestLS : Set :=
 | emptyRequestLS : RequestLS
 | ConsRequestLS : RequestItem -> RequestLS -> RequestLS.
 
 (* Now we get into functions needed to define the getProtocol function. 
    Due to coqs linear nature, we must define in this order, but know that
    it's existence was only deamed necessary during the construction of getProtocol. 
    
    In short, the purpose of this function is to reduce the size of the list of the 
    things we are waiting on measurements for. The option type is used to indicate
    if the requirement posed upon the value v has failed to be met.
    *)
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
 
Definition canSend (ls : list Description) (priv : PrivacyPolicy) : option Description :=
(match ls with
 | nil => None
 | cons d ds => 
   (match (handleRequest priv d) with 
     | (_, Sendable_Measurement d _,_) => Some d  
     | _ => None
     end)
end).
   
(* the above is only a definition. this helps us make sure we respond "in order" *)

Fixpoint reducePrivacy (d : Description) (v : (measurementDenote d)) (priv : PrivacyPolicy) : PrivacyPolicy.
refine (
match priv with
 | EmptyPolicy => EmptyPolicy
 | @ConsPolicy dp rule_d pp' =>
      match rule_d with
       | @rule _ your reqrment => if (eq_dec_Description d your) then
          (match reqrment with
            | requirement _ f => if (f _) then ConsPolicy (free dp) (reducePrivacy d v pp')
                               else ConsPolicy (never dp) (reducePrivacy d v pp')
          end)
          else (ConsPolicy (rule your reqrment) (reducePrivacy d v pp'))
       | _ => @ConsPolicy dp rule_d (reducePrivacy d v pp')
      end
    
 end). subst. exact v. Defined.
 
Fixpoint getProtocol (n : nat) (a: Action) (myPriv : PrivacyPolicy) 
 (toRequest : RequestLS) (unresolved : RequestLS) (toSend : list Description): Session :=
(match n with
| O => match a with 
    | ASend => (Send StopMessage) Stop
    | AReceive => Receive (fun m => Stop) 
    end
| S n' =>
(match a with
 | ASend => 
   (match (canSend toSend myPriv) with
     | Some d => 
      (* if there was something queued up, I should expect to receive something since we are excluding 'and' *)
      Send (Sendable_Measurement d (measure d)) (getProtocol n' AReceive myPriv toRequest unresolved (tail toSend))
     | None => 
     (*I've been told I have to send something. I either am not allowed to send the thing, or 
     there was nothing to send. No matter what, the other guy is expecting a send, so send we must. *)
      (match toRequest with
     | emptyRequestLS => Send StopMessage Stop (* If I can't send a measurment and I have nothing to request,
       I guess we're done. *)
     | ConsRequestLS reqItem reqls' => (match reqItem with
         | requestItem d reqment => Send (RequestS d) (*Something to request! I sent, so now I expect to receive with reduced torequest state, but built up unresolved state*) 
            (getProtocol n' AReceive myPriv reqls' 
               (ConsRequestLS (requestItem d reqment) unresolved) toSend )
         end)
     end)
    end)
 
 
 
(* I've been instructed to receive. As per our agreement, always send right after a receive.
Unless, of course, it was a StopMessage, then stop. *)
 | AReceive => Receive (fun m => match m with
             | Sendable_Measurement d v => (match reduceUnresolved d v unresolved with
                 | Some newUnresolvedState => 
                    getProtocol n' ASend (reducePrivacy d v myPriv) toRequest newUnresolvedState toSend
                 | None => Send StopMessage Stop (*fails to meet my reqs I give up *)
                 end) 
             | RequestS d => (match handleRequest myPriv d with 
                 | (_, StopMessage,_) => Send StopMessage Stop
                 | (newpp,mess,reqItem) => Send mess 
                     (getProtocol n' AReceive newpp emptyRequestLS (ConsRequestLS reqItem unresolved) toSend)
                 end)
             | StopMessage => Stop
             end)
 end)
 end). 
Ltac findForExists hypo := match goal with
| [ hypo :context[?T]   |- exists T, _ ] => exists T; (try reflexivity)
  end.
 
Require Import Omega. 
Theorem WillReceive : forall n a pp rls un ls m s, m <> StopMessage ->  (getProtocol (S n) a pp rls un ls) = Send m s -> 
 exists f, s = Receive f. 
Proof. intro n. induction n. intros. simpl in H0. destruct a. destruct (canSend ls pp).
findForExists H0. inversion H0.  reflexivity. destruct rls.
inversion H0. subst. elim H. reflexivity. destruct r.
findForExists H0. inversion H0. reflexivity. inversion H0.
intros. simpl in H0. destruct a. destruct (canSend ls pp). inversion H0. eauto.
 destruct rls. inversion H0. subst. elim H. reflexivity. destruct r. inversion H0. 
findForExists H3. inversion H0. Qed.

Add LoadPath "C:\Users\Paul\Documents\coqs\protosynth\cpdt\src".
Require Import CpdtTactics. 
Theorem WillSend : forall n a pp rls un ls f, (getProtocol (S n) a pp rls un ls) = Receive f -> 
( forall m, m <> StopMessage -> exists m2 s', (f m) = Send m2 s').
Proof. intro n. induction n. intros. simpl in H. destruct a. destruct (canSend ls pp). inversion H.
destruct rls. inversion H. destruct r. inversion H. inversion H. destruct m eqn : M. destruct (reduceUnresolved d m0 un). eauto. eauto.
destruct (handleRequest pp d). destruct p. destruct m0. exists (Sendable_Measurement d0 m0). eauto. eauto. eauto.
elim H0. reflexivity. intros. simpl in H. destruct a. destruct (canSend ls pp). inversion H. subst. destruct rls. inversion H.
destruct r. inversion H. simpl_eq. simpl in H. destruct m. inversion H. subst.
destruct (reduceUnresolved d m un). destruct (canSend ls (reducePrivacy d m pp)).
eauto. destruct rls. eauto. destruct r0. eauto. eauto. inversion H. destruct (handleRequest pp d). destruct p.
destruct m. eauto. eauto. eauto. elim H0. reflexivity.
Qed.

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

Definition attesterproto1 := getProtocol 5 AReceive lenientPolicy emptyRequestLS emptyRequestLS nil .
Definition appraiserProto1 := getProtocol 5 ASend EmptyPolicy thingsIwant emptyRequestLS nil.

Definition attesterproto2 := getProtocol 5 AReceive EmptyPolicy emptyRequestLS emptyRequestLS nil.
Definition appraiserProto2 := getProtocol 5 ASend EmptyPolicy thingsIwant emptyRequestLS nil.

Definition attesterproto3 := getProtocol 5 AReceive lenientishPolicy emptyRequestLS emptyRequestLS nil.
Definition appraiserProto3 := getProtocol 5 ASend lenientPolicy thingsIwant emptyRequestLS nil.


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

Definition smallStep (dos : (Session * Session)) : option (Session * Session):=
 match dos with 
  | ((Send m s1'), (Receive f)) => Some (s1', (f m)) 
  | ((Receive f), (Send m s2')) => Some ((f m), s2')
  | _ => None
 end.
 
 Eval cbn in getNext (Sendable_Measurement 
    (descriptor (pcrMR 1)) 1) (getNext _ appraiserProto1). 
Fixpoint smallStepn (n : nat) (x : (Session*Session)): ((Session*Session) *nat) :=
  match n with
  | O => (x,0)
  | S n' => match (smallStep x) with 
              | Some r => smallStepn n'  r
              | None   => (x,n)
            end
  end.

(*
Definition x := Eval cbn in  smallStep (smallStep (smallStep (appraiserProto1, attesterproto1))).
Print x .
*)
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
(*
Eval compute in smallStep (smallStep (smallStep (appraiserProto2, attesterproto2))).  *)
Example eefffees2 : (bigStep appraiserProto2 attesterproto2) = Some (Stop,Stop).
Proof.  unfold appraiserProto2. unfold attesterproto2. simpl.
reflexivity. Qed. 


Theorem IsValid_IsValid : forall x y, IsValid x y -> IsValid y x.
Proof. intros. induction H; auto || eauto.
Qed. 

Theorem bigStep_implies_IsValid : forall x y : Session, (bigStep x y) = Some (Stop,Stop) -> 
 IsValid x y. Proof. intro. induction x. simpl. destruct y eqn:what. simpl.
 intros.
 inversion H.
 intros. apply IHx in H. eauto.
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
Ltac pH H:= match goal with 
  | [ H : IsValid (Send ?M ?X) (Receive ?F) |- _] => 
           apply @lr_send with (F M) in H
  | [ H : context[IsValid (Receive ?F) (Send ?M ?X)] |- _] => 
           apply @rl_send with (F M) in H
  | [ H :context[IsValid Stop Stop] |- _  ] => 
           apply  both_stop in H 
  | [ H : context[IsValid Stop  (Send StopMessage Stop)] |- _] => 
           apply lr_stop in H 
  | [ H : context[IsValid (Send StopMessage Stop) Stop] |- _] => 
           apply rl_stop in H
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

  
  
Theorem WillStop_Receive : forall n a pp rls un f ls, (getProtocol n a pp rls un ls) = Receive f ->
  f StopMessage = Stop. 
Proof. intros.  destruct n. simpl in H. inversion H.
simpl in H. destruct a. destruct (canSend ls pp).  inversion H.
destruct rls.  inversion H.
destruct r. inversion H. inversion H. reflexivity.
simpl in H. destruct a. destruct (canSend ls pp). inversion H. destruct rls.
inversion H. destruct r. inversion H. inversion H. reflexivity.          
Qed.

Theorem willReceive : forall n pp rls un ls, exists f, (getProtocol (S n) AReceive pp rls un ls) = Receive f. 
Proof. intros. destruct n. simpl. eauto. simpl. eauto.
Qed.

Theorem IsValid_WillStoprl : 
 forall n pp rls un ls, IsValid (getProtocol (S n) AReceive pp rls un ls) (Send StopMessage Stop).
 intros. proto_simpler. proto_simpler. auto. auto. Qed.
 
Theorem IsValid_WillStoplr : 
 forall n pp rls un ls, IsValid (Send StopMessage Stop) (getProtocol (S n) AReceive pp rls un ls).
  intros. proto_simpler. proto_simpler. auto. auto. Qed.

Theorem WillStop_Send : forall n a pp rls un r ls, (getProtocol n a pp rls un ls) = Send StopMessage r ->
  r = Stop. 
Proof. intros. destruct n. simpl in H. inversion H.
simpl in H. destruct a. destruct (canSend ls pp). inversion H.
destruct rls. inversion H. reflexivity.    
destruct r0. inversion H. inversion H. refl. inversion H. refl.
inversion H. simpl in H. destruct a. destruct (canSend ls pp). inversion H. destruct rls. inversion H. refl.
destruct r. destruct r0. inversion H. destruct r0. inversion H. destruct r0. inversion H.
destruct r0. inversion H. inversion H. Qed.

Theorem wellduh_eq_dec_Adjective :
 forall x, exists p : x =x, eq_dec_adjective  x x= left p.
 intros. case_eq (eq_dec_adjective x x). intros. exists e. reflexivity.
 intros. assert (x = x). refl. contradiction. Qed.
 
 Theorem wellduh_eq_dec_Noun :
forall x, exists p : x =x, eq_dec_noun  x x= left p.
 intros. case_eq (eq_dec_noun x x). intros. exists e. reflexivity.
 intros. assert (x = x). refl. contradiction. Qed.
 
Theorem wellduh_eq_dec_Description : 
forall x, exists p : x = x, eq_dec_Description x x = left p.
 intros. case_eq (eq_dec_Description x x). intros. exists e. reflexivity.
 intros. assert (x = x). refl. contradiction. Qed.
 
 
Theorem IguessThatsOkay :
IsValid Stop ((Receive (fun _ => Stop))).
Admitted.

Ltac elim_let := match goal with 
  | [  |- IsValid _ (let _ := ?T in _) ] => destruct T
  | [  |- IsValid  (let _ := ?T in _) _ ] => destruct T
  | [  |- context[let _ := ?T in _] ] => destruct T
  | [  |- let _ := ?T in _ ] => destruct T
  
  end.
  (*
  Add LoadPath "C:\Users\Paul\Documents\coq\cpdt".
Require Import CpdtTactics.  *)
Theorem IsValid_inc1 : forall  pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  IsValid (getProtocol (1) ASend pp1 rls1 un1 ls1) (getProtocol (1) AReceive pp2 rls2 un2 ls2).
  Proof. intros. simpl. destruct rls1. destruct (canSend ls1 pp1). proto_simpler.
  destruct (reduceUnresolved d (measure d) un2).  auto. auto.
  destruct (reduceUnresolved d (measure d) un2). eauto. eauto.  eauto.
  proto_simpler. proto_simpler.  auto. auto.
  destruct (canSend ls1 pp1). proto_simpler.
  destruct (reduceUnresolved d (measure d) un2). eauto. eauto. 
  destruct (reduceUnresolved d (measure d) un2). auto. auto.        
  destruct r. proto_simpler. destruct (handleRequest pp2 d). destruct p. destruct m.
  proto_simpler.   eauto. apply IguessThatsOkay. auto.
  proto_simpler. apply IguessThatsOkay. auto.
  proto_simpler. auto. auto.      
  destruct (handleRequest pp2 d). destruct p. reflexivity.
  Qed. 

Theorem IsValid_inc2 : forall  pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  IsValid (getProtocol 2 ASend pp1 rls1 un1 ls1) (getProtocol 2 AReceive pp2 rls2 un2 ls2).
  Proof. intros. simpl. destruct (canSend ls1 pp1). proto_simpler. proto_simpler.
  destruct (reduceUnresolved d (measure d) un2). 
  destruct (canSend ls2 (reducePrivacy d (measure d) pp2)). proto_simpler.
  destruct (reduceUnresolved d0 (measure d0) un1). auto. auto.
  destruct (reduceUnresolved d0 (measure d0) un1). auto. auto.
  destruct rls2. proto_simpler. auto. auto.
  destruct r0.   proto_simpler. destruct (handleRequest pp1 d0). destruct p.
  destruct m. admit. admit. auto.       
  destruct (handleRequest pp1 d0). destruct p. destruct m. auto. auto. auto.
  proto_simpler. auto. auto.
  destruct (reduceUnresolved d (measure d)  un2).
  destruct (canSend ls2 (reducePrivacy d (measure d) pp2)). auto.
  destruct rls2. auto.
  destruct r0. auto. auto.
  destruct rls1. proto_simpler. proto_simpler. auto. auto.
  destruct r. proto_simpler. proto_simpler.      
  destruct (handleRequest pp2 d). destruct p.   
  destruct m. proto_simpler.   
  destruct (eq_dec_Description d d0). destruct r. simpl_eq. subst. eauto. simpl_eq.
  auto. auto. proto_simpler. auto. auto. proto_simpler. auto. auto.
  proto_simpler. auto. auto.
  proto_simpler. auto. auto.
  proto_simpler. auto. auto.
  proto_simpler. auto. auto. auto.
  destruct rls2. eauto.
  destruct r0. proto_simpler.    
  destruct (handleRequest pp1 d0). destruct p. destruct m.
  proto_simpler. admit. auto. proto_simpler. admit. auto. proto_simpler. auto. auto.
  destruct (handleRequest pp1 d0). destruct p. destruct m. auto. auto.
  auto. proto_simpler. auto. auto.
  destruct (reduceUnresolved d (measure d) un2).
  destruct (canSend ls2 (reducePrivacy d (measure d) pp2)). auto.
  destruct rls2. auto. destruct r0. auto. auto.
  destruct rls1. eauto.
  destruct r. proto_simpler. proto_simpler.
  destruct (handleRequest pp2 d). destruct p. destruct m. proto_simpler.    
  destruct (eq_dec_Description d d0). destruct r. subst. simpl.
  destruct (b m). proto_simpler. auto. auto. proto_simpler. auto. auto. destruct (reduceUnresolved d0 m un1). proto_simpler. auto. auto. proto_simpler. auto.
  auto. destruct (eq_dec_Description d d0). destruct r. subst. simpl.
  destruct (b m). auto.    auto. destruct (reduceUnresolved d0 m un1). auto. auto. proto_simpler. destruct (handleRequest pp1 d0). destruct p0. destruct m.
  proto_simpler. destruct r0. destruct (eq_dec_Description d2 d1).
  destruct r0. subst. simpl. destruct (b m). eauto. eauto.
  destruct (reduceUnresolved d1 m un2). eauto. eauto.
  destruct r0. destruct (eq_dec_Description d2 d1). destruct r0.
  subst. simpl. (destruct (b m)). auto. auto. destruct (reduceUnresolved d1 m un2). auto. proto_simpler. proto_simpler. destruct (handleRequest p d1). destruct p1.
  destruct m. proto_simpler. admit. auto.
  proto_simpler. admit. auto. proto_simpler. auto. auto.
  destruct (handleRequest p d1). destruct p1. destruct m.
  auto. auto. auto. proto_simpler. auto. auto.
  destruct (handleRequest pp1 d0). destruct p0.
  destruct m. auto. auto. auto. proto_simpler. auto. auto.
   Abort.


  (*lay out what you're tryng to accomplish (goal/ hypo in one sentence)
    like a one page description of my work (2 or 3 maybe)s
    how to merge with Adam.
  
  *)
  (*
Theorem IsValid_AnyPrivacy : forall n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  IsValid (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol (n) AReceive pp2 rls2 un2 ls2) ->
  forall pp1',
  IsValid (getProtocol (n) ASend pp1' rls1 un1 ls1) (getProtocol (n ) AReceive pp2 rls2 un2 ls2).
  Proof. intros. eauto. intros. eapply IHn.       generalize dependent pp2.  induction pp1. destruct n.  simpl. eauto. intros.  simpl. destruct (canSend ls1 EmptyPolicy). intros.
  destruct (canSend ls1 pp1').   proto.
  destruct (reduceUnresolved d0 (measure d0) un2). eauto.         

Theorem IsValid_Pred : forall n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n) AReceive pp2 rls2 un2 ls2) ->
  IsValid (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol (n ) AReceive pp2 rls2 un2 ls2).
  Proof. simpl. intros. induction n. simpl. eauto. simpl.  
      destruct (canSend ls1 pp1). proto. 
  destruct (reduceUnresolved d (measure d) un2). eauto.    
  apply @lr_send with (m :=(Sendable_Measurement d (measure d))) (f :=(fun m : Message =>
          match m with
          | Sendable_Measurement d v =>
              match reduceUnresolved d v un2 with
              | Some newUnresolvedState =>
                  getProtocol n ASend (reducePrivacy d v pp2) rls2
                    newUnresolvedState ls2
              | None => Send StopMessage Stop
              end
          | RequestS d =>
              let (p, reqItem) := handleRequest pp2 d in
              let (newpp, mess) := p in
              match mess with
              | Sendable_Measurement _ _ =>
                  Send mess
                    (getProtocol n AReceive newpp emptyRequestLS
                       (ConsRequestLS reqItem un2) ls2)
              | RequestS _ =>
                  Send mess
                    (getProtocol n AReceive newpp emptyRequestLS
                       (ConsRequestLS reqItem un2) ls2)
              | StopMessage => Send StopMessage Stop
              end
          | StopMessage => Stop
          end)) in H.  in H. simpl in H.   auto in H.  pH H. .  proto in H. .   intros.  
*)
Theorem IsValid_inc : forall n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  IsValid (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol ( n) AReceive pp2 rls2 un2 ls2) ->
  IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n ) AReceive pp2 rls2 un2 ls2).
  Proof. intro. induction n. intros. simpl. destruct (canSend ls1 pp2). destruct (canSend ls1 pp1). proto.
  destruct (reduceUnresolved d0 (measure d0) un2). proto. auto. auto. proto. auto. auto. destruct (reduceUnresolved d0 (measure d0) un2).
  auto. auto. destruct rls1. proto. auto. auto. destruct r. proto .     destruct (handleRequest pp2 d0). destruct p. destruct m. proto. apply IguessThatsOkay. auto.
  proto. apply IguessThatsOkay. auto. proto. auto. auto. destruct (handleRequest pp2 d0). destruct p. destruct m. auto. auto. auto.
  destruct (canSend ls1 pp1). proto. destruct (reduceUnresolved _ _ _). eauto. eauto. auto.
  destruct rls1. eauto. destruct r. proto. destruct (handleRequest _ _). destruct p. destruct m.
  proto. apply IguessThatsOkay. auto. proto. apply IguessThatsOkay. auto. proto. auto. auto.
  intros. eauto.
  (*Case 2 *)
   intros. simpl. destruct (canSend ls1 pp1). proto. destruct (reduceUnresolved d (measure d) un2). 
   destruct (canSend ls2 (reducePrivacy d (measure d) pp2)). proto. 
   destruct (reduceUnresolved d0 (measure d0) un1). eauto.    intros.  Admitted.


Theorem allGood : forall n pp1 pp2 rls1 un1 un2 ls1 ls2,
 IsValid (getProtocol (S n) ASend pp1 rls1 un1 ls1) (getProtocol (S n) AReceive pp2 emptyRequestLS un2 ls2).
 Proof. intro. induction n. simpl. intros. destruct rls1. destruct (canSend _ _).  proto_simpler. destruct (reduceUnresolved _ _ _).  eauto. eauto. auto.
 proto. auto. auto.  
 destruct r. destruct (canSend ls1 pp1).   proto_simpler. destruct (reduceUnresolved d0 (measure d0)).
proto. destruct (handleRequest pp2 d). auto. auto. eauto. destruct (reduceUnresolved d0 (measure d0) un2). auto. auto.
proto. destruct (handleRequest pp2 d). destruct p. destruct m. proto. apply IguessThatsOkay. auto. proto. apply IguessThatsOkay. auto. proto. auto. auto.
destruct (handleRequest pp2 d). destruct p. destruct m. auto. auto. auto. intros. apply IsValid_inc. apply IHn. Qed.


 Fixpoint reqMember (r : RequestItem) (ls : RequestLS) : bool :=
 match ls with
 | emptyRequestLS => false
 | ConsRequestLS x x0 => if (eq_dec_RequestItem x r) then true else reqMember r x0
 end.
Print smallStep. 
 Definition get_desc (r :RequestItem) : Description :=
  match r with
   | requestItem d x => d
    end.
(*
Theorem goSmall :  forall n pp1 pp2 rls1 rls2 un1 un2 ls1 ls2,
  bigStep (getProtocol (n) ASend pp1 rls1 un1 ls1) (getProtocol ( n) AReceive pp2 rls2 un2 ls2) 
  = Some (Stop, Stop) -> exists p, smallStepn p ((getProtocol (n) ASend pp1 rls1 un1 ls1), (getProtocol ( n) AReceive pp2 rls2 un2 ls2)) = ((Stop,Stop),0).
  Proof. intros. induction n. simpl in H. exists 1. simpl. refl.
    subst.   proto.      *)