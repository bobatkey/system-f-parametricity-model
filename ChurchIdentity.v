Require Import Program.

Require Import Axioms.
Require Import JMUtils.
Require Import TypeSyntax.
Require Import Semantics.
Require Import Shifting.

Set Implicit Arguments.

Definition doublecont : type 0 -> type 0.
intros. 
apply ty_forall.
apply ty_arr.
 apply ty_arr.
  apply shift1. apply H.
  apply ty_var. apply var with (i:=0). constructor.
 apply ty_var. apply var with (i:=0). constructor.
Defined.

Definition doublecontA_to_A : forall t, ty_sem ty_nil (doublecont t) -> ty_sem ty_nil t.
unfold doublecont. intros.
unfold ty_sem in H. simpl in H. destruct H as [x _].
apply (x (ty_sem ty_nil t)). 
intros. eapply coerce.
 apply ty_shift1_equal.
 apply H.
Defined.

Definition A_to_doublecontA : forall t, ty_sem ty_nil t -> ty_sem ty_nil (doublecont t).
intros. unfold ty_sem. unfold doublecont. simpl.
exists (fun A (f:(projT1 (ty_sem_rel (shift1 t)) (A;: ty_nil) -> A)) => f (coerce (sym_eq (ty_shift1_equal t ty_nil A)) H)).
intros.
apply H0.
destruct (shift_sem_rel_eq 0 0 t).
unfold ty_rel in *. unfold shift1. 
rewrite <- H2 with (t1:=H) (t2:=H) (re1:=rel_nil) (re2:=rel_nil) (R:=R).
simpl. change rel_nil with (diagonal ty_nil).
apply <- rel_diagonal. reflexivity.
 symmetry. apply coerce_jmeq.
 symmetry. apply coerce_jmeq.
Defined.

Lemma iso1 : forall ty x, doublecontA_to_A (A_to_doublecontA ty x) = x.
unfold doublecontA_to_A. unfold A_to_doublecontA.
intros. apply coerce_twice.
Save.

Lemma iso2 : forall ty x, A_to_doublecontA ty (doublecontA_to_A x) = x.
unfold A_to_doublecontA. unfold doublecontA_to_A. unfold doublecont. unfold ty_sem.
intros. simpl in x. destruct x as [x P]. simpl.
match goal with [ |- ?x = ?y ] => refine (sig_eq x y _) end. simpl in *.
ext A. ext f.
match goal with [|-_ (coerce ?X (_ _ (fun _ => coerce ?Y _))) = _] => generalize X; generalize Y; intros end.
refine (P (ty_sem ty_nil ty) A
          (fun x y => f (coerce e0 x) = y)
          _ _ _).
intros. clear P.
unfold ty_sem in *.
apply JMeq_eq.
apply f_jmequal; [reflexivity|reflexivity|].
eapply JMeq_trans with (y:=coerce e x1).
 apply coerce_jmeq.
 eapply JMeq_trans with (y:=coerce (sym_eq e0) x2).
  apply eq_JMeq.
   rewrite <- (rel_diagonal ty_nil ty).
   destruct (shift_sem_rel_eq 0 0 ty) as [_ P].
   rewrite P with (re1:=diagonal ty_nil) (re2:=diagonal ty_nil) (R:=fun x y => f (coerce e0 x) = y)
                  (t1':=x1) (t2':=x2).
     apply H.
     apply coerce_jmeq.
     apply coerce_jmeq.
  apply coerce_jmeq.
Save.
