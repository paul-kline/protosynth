Add LoadPath "/users/paulkline/Documents/coqs/protosynth". 
Require Import MyShortHand. 
Require Export ProtoSynthDataTypes.
Require Import ProtoSynthProtocolDataTypes.
Require Import Coq.Program.Equality.
Create HintDb eq_dec_db.

(*Nouns *)
Theorem eq_dec_noun : forall n1 n2 : Noun, {n1 = n2} + {n1 <> n2}.
Proof. intros;  destruct n1, n2; 
  try (left;reflexivity); right; unfold not; intros H; inversion H.
Defined.
Hint Resolve eq_dec_noun : eq_dec_db.

(*Attributes *)
Theorem eq_dec_attribute : forall a1 a2 : Attribute,
                    {a1 = a2} + {a1 <> a2}.
Proof. decide equality; rec_eq.
Defined. 
Hint Resolve eq_dec_attribute : eq_dec_db. 

(*DescriptionR *)
Theorem eq_dec_DescriptionR1 : 
forall n : Noun,
forall a : Attribute,
forall x y : DescriptionR n a,
x = y.
Proof. intros;
induction x; dependent induction y;
( reflexivity).
Defined.
Hint Resolve eq_dec_DescriptionR1 : eq_dec_db.

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

Theorem eq_dec_bool : forall b c : bool, 
{b = c} + {b <> c}.
decide equality.
Defined.
Hint Resolve  eq_dec_bool : eq_dec_db.

Require Import FunctionalExtensionality. 
Theorem eq_dec_f {A} {B} : forall (a b : (A -> B)), a =<> b.
Proof. intros. Admitted.

Theorem eq_dec_Requirement : forall d (x y : Requirement d), x =<> y.
Proof. intros. destruct d, x, y,d; simpl in b, b0; destruct (eq_dec_f b b0); eqdecHelper.  
Qed.
Hint Resolve eq_dec_Requirement : eq_dec_db.

Theorem eq_dec_Action : forall x y : Action,
{x = y} + {x <>y }.
Proof. decide equality. Defined.
Hint Resolve  eq_dec_Action : eq_dec_db.



Theorem eq_dec_RequestItem : forall x y : RequestItem,
 {x = y} + {x <> y}. Proof. intros. destruct x,y. destruct (eq_dec_Description d d0); subst. (destruct r, r0).  eauto. destruct (eq_dec_f b b0);subst. eqdecHelper. destruct d0. simpl in b0,b. destruct d. simpl.
Admitted.

Theorem eq_dec_Role: forall x y : Role, {x = y} + {x <> y}. 
Proof. decide equality. Defined.
Hint Resolve eq_dec_Role. 

Theorem eq_dec_VarID : forall x y : VarID, {x = y} + {x <> y}.
Proof. intros. destruct x,y; 
  (left; reflexivity) || 
  (decide equality; rec_eq) ||
  (right; unfold not;intros;inversion H).
Defined.

Theorem eq_dec_Participant : forall x y : Participant, {x = y} + {x <> y}.
 Proof. decide equality. Defined.
