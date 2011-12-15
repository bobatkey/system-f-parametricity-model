Require Import Program.
Require Import Axioms.

Set Implicit Arguments.

Theorem f_jmequal2 :
  forall (A1 A1' A2 A2' B:Type) (f:A1 -> A2 -> B) (g:A1' -> A2' -> B)
    (x1:A1) (y1:A1') (x2:A2) (y2:A2'),
    JMeq f g -> JMeq x1 y1 -> JMeq x2 y2 -> f x1 x2 = g y1 y2.
Proof.
  intros. destruct H0. destruct H1. rewrite (JMeq_eq H). reflexivity.
Qed.

Definition coerce_aux : forall (A B:Set),
  B = A -> { f : A -> B | forall x, JMeq (f x) x }.
intros A B eq. rewrite <- eq. exists (fun (x:B) => x). intro x. reflexivity.
Defined.

Definition coerce : forall (A B:Set),
  B = A -> A -> B.
intros. apply (projT1 (coerce_aux H) H0).
Defined.

Lemma coerce_jmeq : forall (A B : Set) (eql : A = B) x,
  JMeq (coerce eql x) x.
intros. unfold coerce.
destruct (coerce_aux eql).
simpl. apply j. 
Save.

Theorem f_jmequal :
  forall (A1 A1' B B':Set) (f:A1 -> B) (g:A1' -> B')
    (x1:A1) (y1:A1'),
    B = B' ->
    JMeq f g -> JMeq x1 y1 -> JMeq (f x1) (g y1).
Proof.
  intros. destruct H. destruct H1. rewrite (JMeq_eq H0). reflexivity.
Qed.

Theorem f_jmequal_type :
  forall (A1 A1':Type) (B:A1 -> Set) (B':A1'->Set)
         (f:forall a, B a) (g:forall a, B' a)
    (x1:A1) (y1:A1'),
    (forall a a', JMeq a a' -> B a = B' a') ->
    JMeq f g -> JMeq x1 y1 -> JMeq (f x1) (g y1).
intros.
destruct H1.
assert (B = B'). ext a. apply H. reflexivity.
revert f g H0. rewrite H1. intros. rewrite H0. reflexivity.
Save.

Lemma jmeq_exist : forall (A B:Set) (x:A) (x':B) (P:A->Prop) (Q:B->Prop) p p',
  A = B ->
  (forall a b, JMeq a b -> P a = Q b) ->
  JMeq (exist P x p) (exist Q x' p') ->
  JMeq x x'.
intros.
destruct H.
assert (P = Q). ext a. apply H0. reflexivity.
destruct H. 
assert (exist P x p = exist P x' p'). apply JMeq_eq. apply H1.
inversion H.
destruct H3. reflexivity.
Save.

Lemma coerce_twice : forall (A B:Set) (eqp:A = B) (eqp':B=A) x,
  coerce eqp (coerce eqp' x) = x.
intros.
apply JMeq_eq. eapply JMeq_trans; apply coerce_jmeq.
Save.

Lemma coerce_twice_jmeq : forall (A B C:Set) (eqp:A = B) (eqp':B=C) x,
  JMeq (coerce eqp (coerce eqp' x)) x.
intros.
eapply JMeq_trans; apply coerce_jmeq.
Save.

Lemma eq_JMeq : forall A (x y:A), x = y -> JMeq x y.
intros. rewrite H. reflexivity.
Save.
