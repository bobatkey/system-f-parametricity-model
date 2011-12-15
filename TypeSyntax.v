Require Import Arith.
Require Import Program.
Require Import Compare_dec.

Set Implicit Arguments.

(*
(* This is here because the standard library declares plus_comm to be
   opaque *)
Lemma plus_0 : forall m, m = m + 0.
induction m. reflexivity. change (S m + 0) with (S (m + 0)). rewrite <- IHm. reflexivity.
Defined.

Lemma plus_S : forall n m, S n + m = n + S m.
intros. induction n.
 reflexivity.
 simpl. rewrite <- IHn. reflexivity.
Defined.

Lemma plus_comm_transparent : forall n m, n + m = m + n.
induction n.
 intro m. apply plus_0.
 intros. rewrite <- plus_S. change (S n + m) with (S (n + m)). rewrite IHn. reflexivity.
Defined.
*)

(******************************************************************************)

Inductive variable : nat -> Set :=
| var : forall g i, i < g -> variable g.

Inductive type : nat -> Set :=
| ty_var    : forall g, variable g -> type g
| ty_arr    : forall g, type g -> type g -> type g
| ty_forall : forall g, type (S g) -> type g.

Definition shift_var : forall g c,
  variable (c + g) -> variable (c + 1 + g).
intros g c v. inversion v. subst.
destruct (le_lt_dec c i).
 apply var with (i:=S i). rewrite (plus_comm c 1). simpl. apply lt_n_S. assumption.
 apply var with (i:=i). rewrite <- plus_assoc. simpl. rewrite <- plus_Snm_nSm. apply le_S. assumption.
Defined.

Definition shift (g : nat) (c : nat) :
  type (c + g) -> type (c + 1 + g).
intros.
set (g':=c+g) in *. set (e:=refl_equal g' : g' = c+g). generalize g' H c e. clear g' H c e. intros g' H.
induction H; intros; subst.
 (* ty_var *)
 apply ty_var. apply shift_var. apply v.
 (* ty_arr *)
 apply ty_arr.
  apply IHtype1. reflexivity.
  apply IHtype2. reflexivity.
 (* ty_forall *)
 apply ty_forall.
  change (S (c + 1 + g)) with ((S c) + 1 + g).
  apply IHtype. reflexivity.
Defined.

Definition shift1 : forall g, type g -> type (S g).
intros.
change (S g) with (0 + 1 + g). 
apply shift with (c:=0). apply H.
Defined.

Definition subst_var (g c d : nat) (v : variable d) : 
 d = c + 1 + g ->
 type (c + g) -> type (c + g).
intros. destruct v. subst.
destruct (lt_eq_lt_dec i c) as [[X|X]|X].
 apply ty_var. apply var with (i:=i). apply lt_plus_trans. assumption.
 apply H0.
 destruct (O_or_S i) as [[i' i_eq_Si'] | i_eq_0].
  apply ty_var. apply var with (i:=i'). subst. rewrite (plus_comm c 1) in l. simpl in l. apply lt_S_n. assumption.
  elimtype False. subst. inversion X.
Defined.

Definition subst (g : nat) (c : nat) :
  type (c + g) ->
  type (c + 1 + g) ->
  type (c + g).
intros. dependent induction H0.
 (* ty_var *)
 apply subst_var with (d:=c + 1 + g). assumption. reflexivity. assumption.
 (* ty_arr *)
 apply ty_arr.
  apply IHtype1. apply H. reflexivity.
  apply IHtype2. apply H. reflexivity.
 (* ty_forall *)
 apply ty_forall.
 apply IHtype with (c0:=S c). apply shift1. apply H. reflexivity.
Defined.

Definition type_subst1 : forall g, type (S g) -> type g -> type g.
intros. 
change g with (0 + g).
apply subst. apply H0. apply H.
Defined.
