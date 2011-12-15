Require Import Arith.
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

Record preorder (W:Type) : Type := mkPorder
  { preorder_order  :> W -> W -> Prop
  ; preorder_refl   : forall x, preorder_order x x
  ; preorder_trans  : forall x y z, preorder_order x y -> preorder_order y z -> preorder_order x z 
  }.

Definition kripke_relation (W:Type) (Worder:preorder W) (A B:Set) (R:W -> A -> B -> Prop) :=
  forall x y a b, Worder x y -> R x a b -> R y a b.

Definition w_eq := fun (W:Type) (A:Set) (w:W) (a b:A) => a = b.

Lemma w_eq_kripke : forall W (Worder:preorder W) A,
  kripke_relation Worder (@w_eq W A).
intros. unfold kripke_relation. unfold w_eq. auto.
Save.

Inductive rel_environment (W:Type) (Worder:preorder W) : forall n, ty_environment n -> ty_environment n -> Type :=
| rel_nil  : rel_environment Worder ty_nil ty_nil
| rel_cons : forall (n:nat) (A B:Set) (env1 env2:ty_environment n) (R:W -> A -> B -> Prop),
  kripke_relation Worder R ->
  rel_environment Worder env1 env2 ->
  rel_environment Worder (A;:env1) (B;:env2).

Notation "R ;; re" := (rel_cons R re) (at level 61, right associativity).

Definition rel_lookup : forall W (Worder:preorder W) i g (l : le (S i) g) e1 e2, rel_environment Worder e1 e2 ->
   W -> lookup l e1 -> lookup l e2 -> Prop.
induction i; intros.
 destruct X.
  elimtype False. inversion l.
  simpl in *. apply R; assumption.
 destruct X.
  elimtype False. inversion l.
  simpl in *. refine (IHi _ _ _ _ X X0 H H0).
Defined.

Lemma rel_lookup_kripke : forall W (Worder:preorder W) (i g : nat) (l:i < g) (e1 e2: ty_environment g) (re:rel_environment Worder e1 e2),
  kripke_relation Worder (rel_lookup l re).
induction i.
 intros. destruct re.
  inversion l.
  simpl in *. unfold kripke_relation. apply k.
 intros. destruct re.
  inversion l.
  simpl in *. unfold kripke_relation. unfold kripke_relation in IHi. 
  intros. apply IHi with (l:=lt_S_n i n l) (e1:=env1) (e2:=env2) (re:=re) (x:=x) (y:=y) (a:=a) (b:=b). 
   assumption.
   assumption.
Save.

Definition rel_lookup_var : forall W (Worder:preorder W) g (v : variable g) e1 e2, rel_environment Worder e1 e2 ->
  W -> lookup_var v e1 -> lookup_var v e2 -> Prop.
intros. destruct v as [g i l]. eapply rel_lookup. 
 apply X. apply X0. apply H. apply H0.
Defined.

Lemma rel_lookup_var_kripke : forall W (Worder:preorder W) (g : nat) (v:variable g) (e1 e2: ty_environment g) (re:rel_environment Worder e1 e2),
  kripke_relation Worder (rel_lookup_var v re).
intros. destruct v. unfold rel_lookup_var.
unfold kripke_relation. apply rel_lookup_kripke.
Save.

Definition diagonal : forall W (Worder:preorder W) (g:nat) (e:ty_environment g), rel_environment Worder e e.
intros. induction e.
 constructor.
 apply rel_cons with (R:=@w_eq W P).
  apply w_eq_kripke.
  assumption.
Defined.

Definition ty_sem_rel (g:nat) (t:type g) :
  { ty_sem : ty_environment g -> Set
  & forall W (Worder:preorder W) (e1 e2 : ty_environment g), rel_environment Worder e1 e2 -> W -> ty_sem e1 -> ty_sem e2 -> Prop }.
induction t.
 (* ty_var *)
 exists (fun e => lookup_var v e).
 intros W Worder e1 e2 re w x1 x2.
 exact (rel_lookup_var v re w x1 x2).
 (* ty_arr *)
 exists (fun e => (projT1 IHt1) e -> (projT1 IHt2) e).
 intros W Worder e1 e2 R w f1 f2.
 exact (forall w' (x1 : projT1 IHt1 e1) (x2 : projT1 IHt1 e2),
               Worder w w' ->
               projT2 IHt1 W Worder e1 e2 R w' x1 x2 ->
               projT2 IHt2 W Worder e1 e2 R w' (f1 x1) (f2 x2)).
 (* ty_forall *)
 exists (fun e => { x : forall (A:Set), (projT1 IHt) (A;:e)
                  | forall W (Worder:preorder W) (A1 A2 : Set) (R : W -> A1 -> A2 -> Prop)
                           (Rkripke:kripke_relation Worder R)
                           w,
                        (projT2 IHt) W Worder (A1;:e) (A2;:e) (Rkripke;;diagonal Worder e) w (x A1) (x A2) }).
 intros W Worder e1 e2 re w x1 x2.
 exact (forall (A1 A2 : Set) (R : W -> A1 -> A2 -> Prop) (Rkripke:kripke_relation Worder R),
           projT2 IHt W Worder (A1;:e1) (A2;:e2) (Rkripke;;re) w (projT1 x1 A1) (projT1 x2 A2)).
Defined.

Definition ty_sem (g:nat) (e:ty_environment g) (t:type g) : Set.
apply (projT1 (ty_sem_rel t) e).
Defined.

Definition ty_rel W (Worder:preorder W) (g:nat) (e1 e2:ty_environment g) (re:rel_environment Worder e1 e2) (t:type g) :
   W -> ty_sem e1 t -> ty_sem e2 t -> Prop.
unfold ty_sem.
intros.
apply (projT2 (ty_sem_rel t) W Worder e1 e2 re X H H0).
Defined.

Lemma heredity : forall W (Worder:preorder W) (g:nat) (e1 e2:ty_environment g) (re:rel_environment Worder e1 e2) (ty:type g),
  kripke_relation Worder (ty_rel re ty).
intros. unfold ty_sem in *. unfold ty_rel in *. induction ty.
 (* ty_var *)
 simpl in *. apply rel_lookup_var_kripke.
 (* ty_arr *)
 simpl in *. unfold kripke_relation. intros.
 apply H0.
  apply (preorder_trans Worder) with (y:=y); assumption.
  apply H2.
 (* ty_forall *)
 simpl in *. unfold kripke_relation in *. intros.
 apply IHty with (x:=x).
  assumption.
  apply H0.
Save.

Lemma rel_lookup_diagonal : forall W (Worder:preorder W) g (e:ty_environment g) i (l:le (S i) g) x y w,
  rel_lookup l (diagonal Worder e) w x y <-> x = y.
induction e; intros; simpl in *.
 inversion l.
 destruct i0; simpl.
  reflexivity.
  apply IHe.
Save.

Lemma rel_lookup_var_diagonal : forall W (Worder:preorder W) g (e : ty_environment g) (v : variable g) x y w,
  rel_lookup_var v (diagonal Worder e) w x y <-> x = y.
intros. destruct v as [g i l]. simpl. apply rel_lookup_diagonal.
Save.

Lemma rel_diagonal : forall W (Worder:preorder W) g (e:ty_environment g) ty w x y,
  ty_rel (diagonal Worder e) ty w x y <-> x = y.
unfold ty_rel. unfold ty_sem. induction ty; simpl; intros.
 (* ty_var *)
 apply rel_lookup_var_diagonal.
 (* ty_arr *)
 split; intros.
  ext z. rewrite <- IHty2. apply H. apply (preorder_refl Worder). rewrite IHty1. reflexivity.
  rewrite IHty2. rewrite IHty1 in H1. subst. reflexivity.
 (* ty_forall *)
 destruct x as [x x_rel]. destruct y as [y y_rel]. simpl in *.
 split; intros.
  apply sig_eq. simpl. ext A. rewrite <- IHty. apply H.
  inversion H. subst. apply x_rel.
Save.
