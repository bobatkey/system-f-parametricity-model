Require Import JMeq.

Set Implicit Arguments.

Axiom proof_irrelevance : forall (P : Prop) (p1 p2:P), p1 = p2.

Lemma sig_eq : forall (A:Set) (P:A -> Prop) (x1 x2: sig P),
  projT1 x1 = projT1 x2 -> x1 = x2.
intros A P x1 x2 Heq. destruct x1. destruct x2. simpl in Heq.
revert p p0. rewrite Heq. intros p p0. rewrite (proof_irrelevance p p0).
reflexivity.
Save.

Axiom ext : forall (A:Type) (B:A->Type) (f g : forall a, B a), (forall x : A, f x = g x) -> f = g.

Ltac ext A := apply ext; intros A.

(*Axiom pred_ext : forall (A : Type) (P Q : A -> Prop),
  (forall x, P x <-> Q x) -> P = Q.
*)

Axiom prop_ext : forall (P Q:Prop), (P <-> Q) -> P = Q.

Lemma pred_ext2 : forall (A B : Type) (P Q : A -> B -> Prop),
  (forall x y, P x y <-> Q x y) -> P = Q.
intros. ext a. ext b. apply prop_ext. apply H.
Save.

Lemma subset_type_eq : forall (A B:Set) (P : A -> Prop) (Q : B -> Prop),
  A = B ->
  (forall a b, JMeq a b -> (P a = Q b)) ->
  { a : A | P a } = { b : B | Q b }.
intros A B P Q ABeq. 
destruct ABeq. intros.
assert (P = Q). 
ext a. apply H. reflexivity.
destruct H0. reflexivity.
Save.

Lemma set_forall_ext : forall (A B : Set -> Set), (forall a, A a = B a) -> (forall a, A a) = (forall a, B a).
intros. assert (A = B).
ext a. apply H. rewrite H0. reflexivity.
Defined.

Lemma forall_ext : forall (A:Type) (P Q : A -> Prop), (forall a, P a = Q a) -> (forall a, P a) = (forall a, Q a).
intros.
assert (P = Q) by (ext a; apply H).
rewrite H0. reflexivity.
Save.

Lemma forall_ext2 : forall (A B:Set) (P Q : A -> B -> Prop), (forall a b, P a b = Q a b) -> (forall a b, P a b) = (forall a b, Q a b).
intros.
assert (P = Q) by (ext a; ext b; apply H).
rewrite H0. reflexivity.
Save.
