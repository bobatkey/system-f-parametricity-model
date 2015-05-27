Set Implicit Arguments.

Require Import List.
Require Import Arith.
Require Import Program.

Require Import Axioms.
Require Import JMUtils.
Require Import TypeSyntax.
Require Import KripkeSemantics.

Definition app : forall g1 g2, ty_environment g1 -> ty_environment g2 -> ty_environment (g1 + g2).
intros. dependent induction X.
 apply X0.
 apply ty_cons. apply P. apply IHX. apply X0.
Defined.

Definition re_app : forall W (Worder:preorder W) g1 g2 (e11 e12 : ty_environment g1) (e21 e22 : ty_environment g2),
  rel_environment Worder e11 e12 -> rel_environment Worder e21 e22 -> rel_environment Worder (app e11 e21) (app e12 e22).
intros. dependent induction X.
 apply X0.
 eapply rel_cons. apply k. apply IHX. apply X0.
Defined.

Lemma diagonal_app : forall W (Worder:preorder W) g1 g2 (e1 : ty_environment g1) (e2 : ty_environment g2),
  diagonal Worder (app e1 e2) = re_app (diagonal Worder e1) (diagonal Worder e2).
induction e1; intros; simpl.
 reflexivity.
 rewrite IHe1. reflexivity.
Save.

(* FIXME: factor this out from Shifting.v as well *)
Definition var_eq : forall g1 g2 (v : variable (g1 + g2))
  (e1 : ty_environment g1) (e2 : ty_environment g2) (A : Set),
  lookup_var v (app e1 e2) =
  lookup_var (shift_var g2 g1 v) (app (app e1 (A;: ty_nil)) e2).
intros. dependent destruction v.
simpl. destruct (le_lt_dec g1 i).
 (* g1 <= i *)
 unfold lookup_var. revert g1 e1 g2 e2 l l0. induction i; intros.
  (* i = 0 *)
  inversion l0. subst. dependent destruction e1. simpl. apply f_equal. apply proof_irrelevance.
  (* i > 0 *)
  dependent destruction e1.
   (* e1 = ty_nil *)
   simpl. apply f_equal. apply proof_irrelevance.
   (* e1 = ty_cons ... *)
   simpl. rewrite IHi. simpl. apply f_equal. apply proof_irrelevance. apply le_S_n. apply l0.
 (* i < g1 *)
 unfold lookup_var. revert g1 e1 g2 e2 l l0. induction i; intros.
  (* i = 0 *)
  dependent destruction e1.
   (* e1 = ty_nil *)
   inversion l0.
   (* e1 = ty_cons ... *)
   simpl. reflexivity.
  (* i > 0 *)
  dependent destruction e1.
   (* e1 = ty_nil *)
   inversion l0.
   (* e1 = ty_cons ... *)
   simpl. rewrite IHi.
   match goal with [ |- (lookup ?x _) = (lookup ?y _) ] => replace x with y end.
   reflexivity. apply proof_irrelevance.
   apply le_S_n. apply l0.
Save.

Lemma rel_eq : forall g1 g2 v,
  forall W (Worder:preorder W) (e11 e12 : ty_environment g1) (e21 e22 : ty_environment g2)
    (re1 : rel_environment Worder e11 e12) (re2 : rel_environment Worder e21 e22)
    (A1 A2 : Set) (R : W -> A1 -> A2 -> Prop)
    (Rkripke : kripke_relation Worder R)
    (t1 : lookup_var v (app e11 e21))
    (t2 : lookup_var v (app e12 e22))
    (t1' : lookup_var (shift_var g2 g1 v) (app (app e11 (A1;: ty_nil)) e21))
    (t2' : lookup_var (shift_var g2 g1 v) (app (app e12 (A2;: ty_nil)) e22))
    (w : W),
    JMeq t1 t1' ->
    JMeq t2 t2' ->
    rel_lookup_var v (re_app re1 re2) w t1 t2 =
    rel_lookup_var (shift_var g2 g1 v) (re_app (re_app re1 (Rkripke;; (rel_nil Worder))) re2) w t1' t2'.
intros g1 g2 v W Worder e11 e12 e21 e22 re1 re2 A1 A2 R Rkripke t1 t2 t1' t2' w eq1 eq2.
dependent destruction v.
simpl in *. destruct (le_lt_dec g1 i).
 (* g1 <= i *)
 revert g1 e11 e12 re1 g2 e21 e22 re2 l t1 t2 t1' t2' l0 eq1 eq2. induction i; intros.
  (* i = 0 *)
  inversion l0. subst. dependent destruction re1. simpl in *. 
  match goal with [ |- _ ?X _ _ = _ ?Y _ _ ] => set (y:=Y) in * end. 
  assert (l = y). apply proof_irrelevance. generalize y t1' eq1 t2' eq2 H. clear y t1' eq1 t2' eq2 H. intros. subst y.
  apply f_jmequal2.
   reflexivity.
   assumption.
   assumption.
  (* i > 0 *)
  dependent destruction re1.
   (* re1 = rel_nil *)
   simpl in *. 
   match goal with [ |- _ ?X _ _ = _ ?Y _ _ ] => set (y:=Y) in * end. 
   assert (l = y). apply proof_irrelevance. generalize y t1' eq1 t2' eq2 H. clear y t1' eq1 t2' eq2 H. intros. subst y.
   apply f_jmequal2.
    reflexivity.
    assumption.
    assumption.
   (* re1 = rel_cons .. *)
   simpl in *. fold plus in *.
   match goal with [ |- _ = _ ?Y _ _ ] => set (y:=Y) in * end. 
   assert (y = (@eq_ind_r nat (S n) (fun n : nat => S i < n + g2)
       (lt_n_S i (n + g2) (lt_S_n i (n + g2) l)) (n + 1) 
       (plus_comm n 1))).
    apply proof_irrelevance.
   generalize y t1' eq1 t2' eq2 H. clear y t1' eq1 t2' eq2 H. intros. subst y.
   rewrite IHi with (l:=lt_S_n i (n + g2) l) (re1:=re1) (re2:=re2) (t1':=t1') (t2':=t2').
    reflexivity.
    apply le_S_n. apply l0.
    assumption.
    assumption.
 (* i < g1 *)
 revert g1 e11 e12 re1 g2 e21 e22 re2 l t1 t2 t1' t2' l0 eq1 eq2. induction i; intros.
  (* i = 0 *)
  dependent destruction re1.
   (* re1 = rel_nil *)
   inversion l0.
   (* re1 = rel_cons ... *)
   simpl. apply f_jmequal2; trivial.
  (* i > 0 *)
  dependent destruction re1.
   (* re1 = rel_nil *)
   inversion l0.
   (* re1 = rel_cons ... *)
   simpl in *. fold plus in *.
   match goal with [ |- _  = _ _ _ _ _ ?X _ _ _ _ _ _ ] => set (x:=X) in * end.
   assert (x= (@eq_ind nat (n + S g2) (fun n : nat => i < n)
       (@eq_ind nat (S (n + g2)) (fun n : nat => i < n)
          (le_S (S i) (n + g2) (lt_S_n i (n + g2) l)) 
          (n + S g2) (plus_Snm_nSm n g2)) (n + 1 + g2) 
       (plus_assoc n 1 g2))).
    apply proof_irrelevance. 
   generalize x t1' t2' eq1 eq2 H. clear x t1' t2' eq1 eq2 H. intros. subst x.
   rewrite IHi with (l:=lt_S_n i (n + g2) l) (re1:=re1) (re2:=re2) (t1':=t1') (t2':=t2'). 
    reflexivity.
    apply le_S_n. apply l0.
    assumption.
    assumption.
Save.

Definition shift_sem_rel_eq : forall g1 g2 ty,
  ( forall (e1 : ty_environment g1) (e2 : ty_environment g2) A,
      ty_sem (app e1 e2) ty = ty_sem (app (app e1 (A;:ty_nil)) e2) (shift g2 g1 ty) )
  /\
  ( forall W (Worder:preorder W) (e11 e12 : ty_environment g1) (e21 e22 : ty_environment g2)
           (re1 : rel_environment Worder e11 e12) (re2 : rel_environment Worder e21 e22)
           (A1 A2 : Set) (R : W -> A1 -> A2 -> Prop) (Rkripke : kripke_relation Worder R) t1 t2 t1' t2' w,
           JMeq t1 t1' ->
           JMeq t2 t2' ->
           ty_rel (re_app re1 re2) ty w t1 t2 =
           ty_rel (re_app (re_app re1 (Rkripke;;(rel_nil Worder))) re2) (shift g2 g1 ty) w t1' t2').
intros g1 g2 ty.
dependent induction ty.
 (* ty_var *)
 unfold ty_sem. simpl.
 split.
  (* types *)
  apply var_eq.
  (* relations *)
  apply rel_eq.
 (* ty_arr *)
 change (shift g2 g1 (ty_arr ty1 ty2)) with (ty_arr (shift g2 g1 ty1) (shift g2 g1 ty2)).
 unfold ty_sem in *. unfold ty_rel in *. simpl in *.
 destruct IHty1 as [ty_eq1 rel_eq1].
 destruct IHty2 as [ty_eq2 rel_eq2].
 split.
  (* types *)
  intros. rewrite ty_eq1 with (e1:=e1) (e2:=e2) (A:=A). rewrite ty_eq2 with (e1:=e1) (e2:=e2) (A:=A). trivial.
  (* relations *)
  intros W Worder e11 e12 e21 e22 re1 re2 A1 A2 R.
  intros. apply prop_ext. split.
   intros.
    pose (tm1 := t1 (coerce (ty_eq1 e11 e21 A1) x1)).
    pose (tm2 := t2 (coerce (ty_eq1 e12 e22 A2) x2)).
    rewrite <- rel_eq2 with (t1:=tm1) (t2:=tm2).
     unfold tm1. unfold tm2. apply H1. assumption.
     rewrite rel_eq1 with (t1':=x1) (t2':=x2) (Rkripke:=Rkripke).
      apply H3.
      apply coerce_jmeq.
      apply coerce_jmeq.
     unfold tm1. apply f_jmequal.
      apply ty_eq2. assumption. 
      apply coerce_jmeq.
     unfold tm2. apply f_jmequal.
      apply ty_eq2. assumption. 
      apply coerce_jmeq.
   intros.
    pose (tm1 := t1' (coerce (sym_eq (ty_eq1 e11 e21 A1)) x1)).
    pose (tm2 := t2' (coerce (sym_eq (ty_eq1 e12 e22 A2)) x2)).
    rewrite rel_eq2 with (t1':=tm1) (t2':=tm2) (Rkripke:=Rkripke).
     unfold tm1. unfold tm2. apply H1. assumption.
     rewrite <- rel_eq1 with (t1:=x1) (t2:=x2) (R:=R).
      apply H3.
      symmetry. apply coerce_jmeq.
      symmetry. apply coerce_jmeq.
     unfold tm1. apply f_jmequal.
      apply ty_eq2.
      assumption. 
      symmetry. apply coerce_jmeq.
     unfold tm2. apply f_jmequal.
      apply ty_eq2.
      assumption. 
      symmetry. apply coerce_jmeq.
 (* ty_forall *)
 change (shift g2 g1 (ty_forall ty)) with (ty_forall (shift g2 (S g1) ty)).
 unfold ty_sem in *. unfold ty_rel in *. simpl in *.
 destruct (IHty (S g1) g2 ty) as [ty_eq IHrel_eq].
  reflexivity.
  reflexivity.
 clear IHty.
 match goal with [|- ?X /\ _]=>assert (ty_eq':X) end.
  (* do types earlier because we need it twice *)
  intros. apply subset_type_eq.
   apply set_forall_ext. intros. apply ty_eq with (e1:=a;:e1) (e2:=e2) (A:=A).
   intros. apply forall_ext with (A:=Type). intro W. apply forall_ext. intro Worder.
           apply forall_ext. intro A1. apply forall_ext. intro A2.
           apply forall_ext. intro R. apply forall_ext. intro Rkripke. apply forall_ext. intro w.
   rewrite diagonal_app. rewrite diagonal_app. rewrite diagonal_app. simpl.
   apply IHrel_eq with (re1:=Rkripke;;diagonal Worder e1) (re2:=diagonal Worder e2) (Rkripke:=@w_eq_kripke W Worder A).
    apply f_jmequal_type with (A1:=Set) (A1':=Set) (f:=a) (g:=b) (x1:=A1) (y1:=A1).
     intros. rewrite H0. apply ty_eq with (e1:=a';:e1) (e2:=e2) (A:=A).
     apply H.
     reflexivity.
    apply f_jmequal_type with (A1:=Set) (A1':=Set) (f:=a) (g:=b) (x1:=A2) (y1:=A2).
     intros. rewrite H0. apply ty_eq with (e1:=a';:e1) (e2:=e2) (A:=A).
     apply H.
     reflexivity.
 split.
  (* types *)
  apply ty_eq'.
  (* relations *)
  intros. 
  apply forall_ext. intro A3. apply forall_ext. intro A4. apply forall_ext. intro R0. apply forall_ext. intro Rkripke0.
  destruct t1. destruct t1'. destruct t2. destruct t2'. simpl in *.
  apply IHrel_eq with (re1:=Rkripke0;;re1) (re2:=re2) (Rkripke:=Rkripke).
   apply f_jmequal_type with (f:=x) (g:=x0) (x1:=A3) (y1:=A3).
    intros. rewrite H1. apply ty_eq with (e1:=a';:e11) (e2:=e21) (A:=A1).
    refine (jmeq_exist _ _ H).
     apply set_forall_ext. intro. apply ty_eq with (e1:=a;:e11) (e2:=e21) (A:=A1).
     intros. apply forall_ext with (A:=Type). intro W'. apply forall_ext. intro W'order. 
             apply forall_ext. intro A5. apply forall_ext. intro A6.
             apply forall_ext. intro R1. apply forall_ext. intro R1kripke. apply forall_ext. intro w'.
     rewrite diagonal_app. rewrite diagonal_app. rewrite diagonal_app. simpl.
     apply IHrel_eq with (re1:=R1kripke;;diagonal W'order e11) (re2:=diagonal W'order e21) (Rkripke:=@w_eq_kripke W' W'order A1).
      apply f_jmequal_type with (A1:=Set) (A1':=Set) (f:=a) (g:=b) (x1:=A5) (y1:=A5).
       intros. rewrite H2. apply ty_eq with (e1:=a';:e11) (e2:=e21) (A:=A1).
        apply H1.
        reflexivity.
      apply f_jmequal_type with (A1:=Set) (A1':=Set) (f:=a) (g:=b) (x1:=A6) (y1:=A6).
       intros. rewrite H2. apply ty_eq with (e1:=a';:e11) (e2:=e21) (A:=A1).
        apply H1.
        reflexivity.
      reflexivity.
   apply f_jmequal_type with (f:=x1) (g:=x2) (x1:=A4) (y1:=A4).
    intros. rewrite H1. apply ty_eq with (e1:=a';:e12) (e2:=e22) (A:=A2).
    refine (jmeq_exist _ _ H0).
     apply set_forall_ext. intro. apply ty_eq with (e1:=a;:e12) (e2:=e22) (A:=A2).
     intros. apply forall_ext with (A:=Type). intro W'. apply forall_ext. intro W'order. 
             apply forall_ext. intro A5. apply forall_ext. intro A6.
             apply forall_ext. intro R1. apply forall_ext. intros R1kripke. apply forall_ext. intro w'.
     rewrite diagonal_app. rewrite diagonal_app. rewrite diagonal_app. simpl.
     apply IHrel_eq with (re1:=R1kripke;;diagonal W'order e12) (re2:=diagonal W'order e22) (Rkripke:=@w_eq_kripke W' W'order A2).
      apply f_jmequal_type with (A1:=Set) (A1':=Set) (f:=a) (g:=b) (x1:=A5) (y1:=A5).
       intros. rewrite H2. apply ty_eq with (e1:=a';:e12) (e2:=e22) (A:=A2).
        apply H1.
        reflexivity.
      apply f_jmequal_type with (A1:=Set) (A1':=Set) (f:=a) (g:=b) (x1:=A6) (y1:=A6).
       intros. rewrite H2. apply ty_eq with (e1:=a';:e12) (e2:=e22) (A:=A2).
        apply H1.
        reflexivity.
      reflexivity.
Save.

Lemma ty_shift1_equal : forall g (ty : type g) e A,
  ty_sem e ty = ty_sem (A;:e) (shift1 ty).
intros.
destruct (shift_sem_rel_eq 0 g ty).
unfold shift1.
apply (H ty_nil e A).
Save.

Lemma rel_shift1_equal : forall g (ty : type g) W (Worder:preorder W)
  (e1 e2 : ty_environment g) (re : rel_environment Worder e1 e2)
  (A1 A2 : Set) (R : W -> A1 -> A2 -> Prop) (Rkripke : kripke_relation Worder R) t1 t2 t1' t2' w,
  JMeq t1 t1' ->
  JMeq t2 t2' ->
  ty_rel re ty w t1 t2 =
  ty_rel (Rkripke;;re) (shift1 ty) w t1' t2'.
intros. 
destruct (shift_sem_rel_eq 0 g ty).
unfold shift1.
apply H2 with (re1:=rel_nil Worder) (Rkripke:=Rkripke); assumption.
Save.

Lemma ty_shift1_twice_equal : forall g (ty : type g) e A B,
  ty_sem e ty = ty_sem (A;:B;:e) (shift1 (shift1 ty)).
intros.
transitivity (ty_sem (B;:e) (shift1 ty)); apply ty_shift1_equal.
Save.

Lemma rel_shift1_twice_equal : forall g (ty : type g) W (Worder:preorder W)
  (e1 e2 : ty_environment g) (re : rel_environment Worder e1 e2)
  (A1 A2 : Set) (RA : W -> A1 -> A2 -> Prop) (RAkripke : kripke_relation Worder RA)
  (B1 B2 : Set) (RB : W -> B1 -> B2 -> Prop) (RBkripke : kripke_relation Worder RB)
  t1 t2 t1' t2' w,
  JMeq t1 t1' ->
  JMeq t2 t2' ->
  ty_rel re ty w t1 t2 =
  ty_rel (RAkripke;;RBkripke;;re) (shift1 (shift1 ty)) w t1' t2'.
intros.
transitivity (ty_rel (RBkripke;;re) (shift1 ty) w (coerce (sym_eq (ty_shift1_equal ty e1 B1)) t1)
                                                  (coerce (sym_eq (ty_shift1_equal ty e2 B2)) t2)).
 apply rel_shift1_equal; symmetry; apply coerce_jmeq.
 apply rel_shift1_equal. 
  eapply JMeq_trans. apply coerce_jmeq. assumption.
  eapply JMeq_trans. apply coerce_jmeq. assumption.
Save.

Definition ty_sem_shift1 : forall g (e : ty_environment g) ty A,
  ty_sem e ty ->
  ty_sem (A;:e) (shift g 0 ty).
intros. eapply coerce. symmetry. apply ty_shift1_equal. assumption.
Defined.

Lemma ty_rel_shift1 : forall g W (Worder:preorder W) (e1 e2:ty_environment g) re ty A1 A2 t1 t2
  R (Rkripke:kripke_relation Worder R) w,
  ty_rel re ty w t1 t2 ->
  ty_rel (Rkripke;;re) (shift1 ty) w (ty_sem_shift1 e1 ty A1 t1) (ty_sem_shift1 e2 ty A2 t2).
intros. refine (coerce _ H). symmetry.
rewrite <- rel_shift1_equal with (t1:=t1) (t2:=t2). 
 reflexivity.
 symmetry. apply coerce_jmeq.
 symmetry. apply coerce_jmeq.
Save.
