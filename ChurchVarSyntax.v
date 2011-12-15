Require Import List.
Require Import Arith.
Require Import Omega.

Require Import Axioms.
Require Import TypeSyntax.
Require Import Semantics.
Require Import ChurchSyntax.

Set Implicit Arguments.

Definition vhoas : type 0.
apply ty_forall.
apply ty_forall.
apply ty_arr.
 apply ty_arr.
  apply ty_var. apply var with (i:=1). constructor.
  apply ty_var. apply var with (i:=0). constructor. constructor.
 apply ty_arr.
  apply ty_arr.
   apply ty_arr.
    apply ty_var. apply var with (i:=1). constructor.
    apply ty_var. apply var with (i:=0). constructor. constructor.
   apply ty_var. apply var with (i:=0). constructor. constructor.
  apply ty_arr.
   apply ty_arr.
    apply ty_var. apply var with (i:=0). constructor. constructor.
    apply ty_arr.
     apply ty_var. apply var with (i:=0). constructor. constructor.
     apply ty_var. apply var with (i:=0). constructor. constructor.
   apply ty_var. apply var with (i:=0). constructor. constructor.
Defined.

Definition hoas_to_vhoas_inner : forall
  (x : forall A : Set, ((A -> A) -> A) -> (A -> A -> A) -> A)
  (P : forall (A1 A2 : Set) (R : A1 -> A2 -> Prop) (x1 : (A1 -> A1) -> A1)
    (x2 : (A2 -> A2) -> A2),
    (forall (x3 : A1 -> A1) (x4 : A2 -> A2),
      (forall (x5 : A1) (x6 : A2), R x5 x6 -> R (x3 x5) (x4 x6)) ->
      R (x1 x3) (x2 x4)) ->
    forall (x3 : A1 -> A1 -> A1) (x4 : A2 -> A2 -> A2),
      (forall (x5 : A1) (x6 : A2),
        R x5 x6 ->
        forall (x7 : A1) (x8 : A2), R x7 x8 -> R (x3 x5 x7) (x4 x6 x8)) ->
      R (x A1 x1 x3) (x A2 x2 x4)),
  forall A : Set,
     {x0
     : forall A0 : Set,
       (A -> A0) -> ((A -> A0) -> A0) -> (A0 -> A0 -> A0) -> A0 |
     forall (A1 A2 : Set) (R : A1 -> A2 -> Prop) (x1 : A -> A1)
       (x2 : A -> A2),
     (forall x3 x4 : A, x3 = x4 -> R (x1 x3) (x2 x4)) ->
     forall (x3 : (A -> A1) -> A1) (x4 : (A -> A2) -> A2),
     (forall (x5 : A -> A1) (x6 : A -> A2),
      (forall x7 x8 : A, x7 = x8 -> R (x5 x7) (x6 x8)) -> R (x3 x5) (x4 x6)) ->
     forall (x5 : A1 -> A1 -> A1) (x6 : A2 -> A2 -> A2),
     (forall (x7 : A1) (x8 : A2),
      R x7 x8 ->
      forall (x9 : A1) (x10 : A2), R x9 x10 -> R (x5 x7 x9) (x6 x8 x10)) ->
     R (x0 A1 x1 x3 x5) (x0 A2 x2 x4 x6)}.
intros.
exists (fun A var lam app => x A (fun f => lam (fun v => f (var v))) app).
intros. apply (P A1 A2).
 intros. apply H0. intros. apply H2. apply H. assumption.
 intros. apply H1. assumption. assumption.
Defined.

Definition hoas_to_vhoas : ty_sem ty_nil hoas -> ty_sem ty_nil vhoas.
unfold ty_sem. unfold hoas. unfold vhoas. simpl.
intros [x P].
exists (hoas_to_vhoas_inner x P).
unfold hoas_to_vhoas_inner. simpl. intros.
apply (P A0 A3).
 intros. apply H0. intros. apply H2. apply H. apply H3.
 intros. apply H1. assumption. assumption.
Defined.

Definition vhoas_to_hoas : ty_sem ty_nil vhoas -> ty_sem ty_nil hoas.
unfold ty_sem. unfold hoas. unfold vhoas. simpl.
intros [x P].
exists (fun A lam app => projT1 (x A) A (fun x => x) lam app).
intros. apply P with (R:=R).
 intros. assumption.
 intros. apply H. intros. apply H1. assumption.
 intros. apply H0. assumption. assumption.
Defined.

Lemma iso1 : forall t, vhoas_to_hoas (hoas_to_vhoas t) = t.
intros. unfold vhoas_to_hoas. unfold hoas_to_vhoas.
unfold ty_sem in t. unfold hoas in t. simpl in t.
destruct t as [x P].
simpl. 
match goal with [ |- ?x = ?y ] => refine (sig_eq x y _) end. 
simpl.
ext A. ext lam. ext appl.
replace (fun f => lam (fun v => f v)) with lam.
 reflexivity.
 ext f. apply f_equal. ext v. reflexivity.
Save.

Lemma iso2 : forall t, hoas_to_vhoas (vhoas_to_hoas t) = t.
intros. unfold vhoas_to_hoas. unfold hoas_to_vhoas. unfold hoas_to_vhoas_inner.
unfold ty_sem in t. unfold hoas in t. simpl in t.
destruct t as [x P].
simpl. 
match goal with [ |- ?x = ?y ] => refine (sig_eq x y _) end. 
simpl. intros. ext V.
match goal with [ |- ?x = ?y ] => refine (sig_eq x y _) end. 
simpl. ext A. ext vari. ext lam. ext appl.
apply P with (A1:=A) (A2:=V) (R:=fun x y => x = vari y) (R0:=fun x y => x = y).
 intros. assumption.
 intros. apply f_equal. ext v. apply H. reflexivity.
 intros. rewrite H. rewrite H0. reflexivity.
Save.
