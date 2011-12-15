Require Import List.

Require Import TypeSyntax.
Require Import Semantics.
Require Import Axioms.
Require Import ChurchNaturals.

Set Implicit Arguments.

Definition church_list : type O.
apply ty_forall.
apply ty_arr.
 (* nil *)
 apply ty_var. apply var with (i:=0). constructor.
 (* cons *)
 apply ty_arr.
  apply ty_arr.
   apply ty_var. apply var with (i:=0). constructor.
   apply ty_arr.
    apply (church_nums 1).
    apply ty_var. apply var with (i:=0). constructor.
  apply ty_var. apply var with (i:=0). constructor.
Defined.

Definition to_list : ty_sem ty_nil church_list -> list (ty_sem ty_nil (church_nums 0)).
intros. unfold ty_sem in H. simpl in H. destruct H. simpl in *.
apply (x (list (ty_sem ty_nil (church_nums 0)))).
 (* nil *)
 apply (nil (A:=(ty_sem ty_nil (church_nums 0)))).
 (* cons *)
 intros.
 apply (cons H0 H).
Defined.

Definition from_list : list (ty_sem ty_nil (church_nums 0)) -> ty_sem ty_nil church_list.
intros. unfold church_list. unfold ty_sem. simpl.
exists (fun A nil cons => list_rec (fun _ => A) nil (fun n _ a => cons a n) H).
induction H.
 auto.
 intros. apply H1.
 apply (IHlist A1 A2 R x1 x2 H0 x0 x3).
  intros. destruct x6. destruct x7. auto.
  destruct a. auto.
Defined.

Lemma list_iso1 : forall l, to_list (from_list l) = l.
intros. unfold to_list. unfold from_list. induction l.
 simpl. reflexivity.
 simpl in *. rewrite IHl. reflexivity.
Save.

Lemma list_iso2 : forall t, from_list (to_list t) = t.
unfold ty_sem. unfold to_list. unfold from_list. simpl in *. intro.
match goal with [ |- ?x = ?y ] => refine (sig_eq x y _) end. simpl in *. destruct t as [t P]. simpl in *.
ext A. ext nilA. ext consA.
(* apply parametricity *)
apply (P (list (ty_sem ty_nil (church_nums 0))) A
         (fun l a => list_rec (fun _ => A) nilA (fun n _ a => consA a n) l = a)).
 (* nil and nilA are related *)
 simpl. reflexivity.
 (* cons and consA are related *)
 simpl. intros. rewrite H. apply f_equal. destruct x0. destruct x3. apply sig_eq. simpl.
 ext B. ext g. ext h. apply H0.
  reflexivity. 
  intros. rewrite H1. reflexivity.
Save.
