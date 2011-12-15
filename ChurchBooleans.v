Require Import TypeSyntax.
Require Import Semantics.
Require Import Axioms.

Definition church_bool : type 0.
apply ty_forall.
 apply ty_arr.
  apply ty_var. apply var with (i:=0). constructor.
  apply ty_arr.
   apply ty_var. apply var with (i:=0). constructor.
   apply ty_var. apply var with (i:=0). constructor.
Defined.

Definition to_bool : ty_sem ty_nil church_bool -> bool.
intros  [cbool _]. simpl in cbool.
apply (cbool bool).
 apply true.
 apply false.
Defined.

Definition from_bool : bool -> ty_sem ty_nil church_bool.
intros. unfold ty_sem. simpl.
exists (fun A t f => match H with true => t | false => f end).
intros. induction H.
 assumption.
 assumption.
Defined.

Lemma bool_iso1 : forall b, to_bool (from_bool b) = b.
unfold to_bool. unfold from_bool. destruct b.
 reflexivity.
 reflexivity.
Save.

Lemma bool_iso2 : forall t, from_bool (to_bool t) = t.
unfold ty_sem. unfold to_bool. unfold from_bool. intro. simpl in *. 
match goal with [ |- ?x = ?y ] => refine (sig_eq x y _) end. simpl in *. destruct t as [t P]. simpl in *.
ext A. ext tr. ext fa.
apply (P bool A (fun b a => (if b then tr else fa) = a)).
 (* true and t *)
 reflexivity.
 (* false and f *)
 reflexivity.
Save.
