Require Import Arith.
Require Import Program.
Require Import Compare_dec.

Require Import Axioms.
Require Import TypeSyntax.

Set Implicit Arguments.

Inductive ty_environment : nat -> Type :=
| ty_nil  : ty_environment 0
| ty_cons : forall i, Set -> ty_environment i -> ty_environment (S i).

Notation "A ;: e" := (ty_cons A e) (at level 61, right associativity).

Definition lookup : forall j i, j < i -> ty_environment i -> Set.
fix 1. intros. destruct j.
 destruct X.
  elimtype False. inversion H.
  apply P.
 destruct X.
  elimtype False. inversion H.
  apply (lookup j i).
   apply lt_S_n. apply H.
   apply X.
Defined.

Definition lookup_var : forall g, variable g -> ty_environment g -> Set.
intros g v e. destruct v as [g i l]. apply (lookup l e). 
Defined.


Inductive rel_environment : forall n, ty_environment n -> ty_environment n -> Type :=
| rel_nil  : rel_environment ty_nil ty_nil
| rel_cons : forall (n:nat) (A B:Set) (env1 env2:ty_environment n),
  (A -> B -> Prop) ->
  rel_environment env1 env2 ->
  rel_environment (A;:env1) (B;:env2).

Notation "R ;; re" := (rel_cons R re) (at level 61, right associativity).

Definition rel_lookup : forall i g (l : le (S i) g) e1 e2, rel_environment e1 e2 ->
   lookup l e1 -> lookup l e2 -> Prop.
induction i; intros.
 destruct X.
  elimtype False. inversion l.
  simpl in *. apply P; assumption.
 destruct X.
  elimtype False. inversion l.
  simpl in *. refine (IHi _ _ _ _ X H H0).
Defined.

Definition rel_lookup_var : forall g (v : variable g) e1 e2, rel_environment e1 e2 ->
  lookup_var v e1 -> lookup_var v e2 -> Prop.
intros. destruct v as [g i l]. eapply rel_lookup. 
 apply X. apply H. apply H0.
Defined.

Definition diagonal : forall (g:nat) (e:ty_environment g), rel_environment e e.
intros. induction e.
 constructor.
 constructor. 
  exact (@eq P).
  assumption.
Defined.

Definition ty_sem_rel (g:nat) (t:type g) :
  { ty_sem : ty_environment g -> Set
  & forall (e1 e2 : ty_environment g), rel_environment e1 e2 -> ty_sem e1 -> ty_sem e2 -> Prop }.
induction t.
 (* ty_var *)
 exists (fun e => lookup_var v e).
 intros e1 e2 re x1 x2.
 exact (rel_lookup_var v re x1 x2).
 (* ty_arr *)
 exists (fun e => (projT1 IHt1) e -> (projT1 IHt2) e).
 intros e1 e2 R f1 f2.
 exact (forall (x1 : projT1 IHt1 e1) (x2 : projT1 IHt1 e2), projT2 IHt1 e1 e2 R x1 x2 ->
                                                            projT2 IHt2 e1 e2 R (f1 x1) (f2 x2)).
 (* ty_forall *)
 exists (fun e => { x : forall (A:Set), (projT1 IHt) (A;:e)
                  | forall (A1 A2 : Set) (R : A1 -> A2 -> Prop),
                        (projT2 IHt) (A1;:e) (A2;:e) (R;;diagonal e) (x A1) (x A2) }).
 intros e1 e2 re x1 x2.
 exact (forall (A1 A2 : Set) (R : A1 -> A2 -> Prop),
           projT2 IHt (A1;:e1) (A2;:e2) (R;;re) (projT1 x1 A1) (projT1 x2 A2)).
Defined.

Definition ty_sem (g:nat) (e:ty_environment g) (t:type g) : Set.
apply (projT1 (ty_sem_rel t) e).
Defined.

Definition ty_rel (g:nat) (e1 e2:ty_environment g) (re:rel_environment e1 e2) (t:type g) :
   ty_sem e1 t -> ty_sem e2 t -> Prop.
unfold ty_sem.
intros.
apply (projT2 (ty_sem_rel t) e1 e2 re H H0). 
Defined.

Lemma rel_lookup_diagonal : forall g (e:ty_environment g) i (l:le (S i) g) x y,
  rel_lookup l (diagonal e) x y <-> x = y.
induction e; intros; simpl in *.
 inversion l.
 destruct i0; simpl.
  reflexivity.
  apply IHe.
Save.

Lemma rel_lookup_var_diagonal : forall g (e : ty_environment g) (v : variable g) x y,
  rel_lookup_var v (diagonal e) x y <-> x = y.
intros. destruct v as [g i l]. simpl. apply rel_lookup_diagonal.
Save.

Lemma rel_diagonal : forall g (e:ty_environment g) ty x y, ty_rel (diagonal e) ty x y <-> x = y.
unfold ty_rel. unfold ty_sem. induction ty; simpl; intros.
 (* ty_var *)
 apply rel_lookup_var_diagonal.
 (* ty_arr *)
 split; intros.
  ext z. rewrite <- IHty2. apply H. rewrite IHty1. reflexivity.
  rewrite IHty2. rewrite IHty1 in H0. subst. reflexivity.
 (* ty_forall *)
 destruct x as [x x_rel]. destruct y as [y y_rel]. simpl in *.
 split; intros.
  apply sig_eq. simpl. ext A. rewrite <- IHty. apply H.
  inversion H. subst. apply x_rel.
Save.
