Require Import TypeSyntax.
Require Import Semantics.
Require Import Axioms.

Set Implicit Arguments.

Lemma lt_0_Sn : forall n, 0 < (S n).
induction n.
 constructor.
 constructor. assumption.
Defined.

Definition church_nums : forall n, type n.
intro n.
apply ty_forall.
apply ty_arr.
 apply ty_var. apply var with (i:=0). apply lt_0_Sn.
 (*apply ty_var.  apply finO.*)
 apply ty_arr.
  apply ty_arr.
   apply ty_var. apply var with (i:=0). apply lt_0_Sn.
   (*apply ty_var. apply finO.*)
   apply ty_var. apply var with (i:=0). apply lt_0_Sn.
   (*apply ty_var. apply finO.*)
  apply ty_var. apply var with (i:=0). apply lt_0_Sn.
  (*apply ty_var. apply finO.*)
Defined.

Definition to_nat : forall n e, ty_sem e (church_nums n) -> nat.
intros. destruct H as [cnat _]. simpl in *.
apply (cnat nat).
 apply 0.
 apply S.
Defined.

Definition from_nat : forall n e, nat -> ty_sem e (church_nums n).
intros. unfold church_nums. unfold ty_sem. simpl.
exists (fun A zero succ => nat_rec (fun n => A) zero (fun _ a => succ a) H).
induction H.
 auto.
 intros. simpl. apply H1. apply (IHnat A1 A2 R x1 x2 H0 x0 x3). apply H1.
Defined.

Lemma nat_iso1 : forall g (e:ty_environment g) n, to_nat (from_nat e n) = n.
intros. unfold to_nat. unfold from_nat. induction n.
 simpl. reflexivity.
 simpl in *. rewrite IHn. reflexivity.
Save.

Lemma nat_iso2 : forall g (e:ty_environment g) t, from_nat e (to_nat t) = t.
unfold ty_sem. unfold to_nat. unfold from_nat. intros. simpl in *.
match goal with [ |- ?x = ?y ] => refine (sig_eq x y _) end. simpl in *. destruct t as [t P].
simpl in *.
ext A. ext zero. ext succ.
(* apply parametricity *)
apply (P nat A (fun n a => nat_rec (fun _ => A) zero (fun _ a => succ a) n = a)).
 (* O and zero are related *)
 simpl. reflexivity.
 (* S and succ are related *)
 simpl. intros. rewrite H. reflexivity.
Save.
