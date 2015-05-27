Set Implicit Arguments.

Require Import List.
Require Import Arith.

Require Import Axioms.
Require Import JMUtils.
Require Import TypeSyntax.
Require Import Semantics.
Require Import Program.

Definition app : forall g1 g2, ty_environment g1 -> ty_environment g2 -> ty_environment (g1 + g2).
intros. dependent induction X.
 apply X0.
 apply ty_cons. apply P. apply (IHX X0).
Defined.

Definition re_app : forall g1 g2 (e11 e12 : ty_environment g1) (e21 e22 : ty_environment g2),
  rel_environment e11 e12 -> rel_environment e21 e22 -> rel_environment (app e11 e21) (app e12 e22).
intros. dependent induction X.
 apply X0.
 apply rel_cons. apply P. apply (IHX X0).
Defined.

Lemma diagonal_app : forall g1 g2 (e1 : ty_environment g1) (e2 : ty_environment g2),
  diagonal (app e1 e2) = re_app (diagonal e1) (diagonal e2).
induction e1; intros; simpl.
 reflexivity.
 rewrite IHe1. reflexivity.
Save.

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
  forall (e11 e12 : ty_environment g1) (e21 e22 : ty_environment g2)
    (re1 : rel_environment e11 e12) (re2 : rel_environment e21 e22)
    (A1 A2 : Set) (R : A1 -> A2 -> Prop)
    (t1 : lookup_var v (app e11 e21))
    (t2 : lookup_var v (app e12 e22))
    (t1' : lookup_var (shift_var g2 g1 v) (app (app e11 (A1;: ty_nil)) e21))
    (t2' : lookup_var (shift_var g2 g1 v) (app (app e12 (A2;: ty_nil)) e22)),
    JMeq t1 t1' ->
    JMeq t2 t2' ->
    rel_lookup_var v (re_app re1 re2) t1 t2 =
    rel_lookup_var (shift_var g2 g1 v) (re_app (re_app re1 (R;; rel_nil)) re2) t1' t2'.
intros g1 g2 v e11 e12 e21 e22 re1 re2 A1 A2 R t1 t2 t1' t2' eq1 eq2.
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
   match goal with [ |- _ _ _ ?X _ _ _ _ _ = _ ?Y _ _ ] => set (y:=Y) in * end.
   assert (y = (@eq_ind_r nat (S n) (fun n : nat => S i < n + g2)
       (lt_n_S i (n + g2) (lt_S_n i (n + g2) l)) (n + 1) 
       (plus_comm n 1))).
    apply proof_irrelevance. generalize y t1' eq1 t2' eq2 H. clear y t1' eq1 t2' eq2 H. intros. subst y.
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
   simpl in *. apply f_jmequal2; trivial.
  (* i > 0 *)
  dependent destruction re1.
   (* re1 = rel_nil *)
   inversion l0.
   (* re1 = rel_cons ... *)
   simpl in *. fold plus in *.
   match goal with [ |- _  = _ _ _ ?X _ _ _ _ _ ] => set (x:=X) in * end.
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
  ( forall (e11 e12 : ty_environment g1) (e21 e22 : ty_environment g2)
           (re1 : rel_environment e11 e12) (re2 : rel_environment e21 e22) (A1 A2 : Set) (R : A1 -> A2 -> Prop) t1 t2 t1' t2',
           JMeq t1 t1' ->
           JMeq t2 t2' ->
           ty_rel (re_app re1 re2) ty t1 t2 =
           ty_rel (re_app (re_app re1 (R;;rel_nil)) re2) (shift g2 g1 ty) t1' t2' ).
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
  intros e11 e12 e21 e22 re1 re2 A1 A2 R.
  intros. apply prop_ext. split.
   intros.
    pose (tm1 := t1 (coerce (ty_eq1 e11 e21 A1) x1)).
    pose (tm2 := t2 (coerce (ty_eq1 e12 e22 A2) x2)).
    rewrite <- rel_eq2 with (t1:=tm1) (t2:=tm2).
     unfold tm1. unfold tm2. apply H1.
     rewrite rel_eq1 with (t1':=x1) (t2':=x2) (R:=R).
      apply H2.
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
    rewrite rel_eq2 with (t1':=tm1) (t2':=tm2) (R:=R).
     unfold tm1. unfold tm2. apply H1.
     rewrite <- rel_eq1 with (t1:=x1) (t2:=x2) (R:=R).
      apply H2.
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
   intros. apply forall_ext. intro A1. apply forall_ext. intro A2. apply forall_ext. intro R.
   rewrite diagonal_app. rewrite diagonal_app. rewrite diagonal_app. simpl.
   apply IHrel_eq with (re1:=R;;diagonal e1) (re2:=diagonal e2) (R:=@eq A).
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
  intros. apply forall_ext. intro A3. apply forall_ext. intro A4. apply forall_ext. intro R0.
  destruct t1. destruct t1'. destruct t2. destruct t2'. simpl in *.
  apply IHrel_eq with (re1:=R0;;re1) (re2:=re2) (R:=R).
   apply f_jmequal_type with (f:=x) (g:=x0) (x1:=A3) (y1:=A3).
    intros. rewrite H1. apply ty_eq with (e1:=a';:e11) (e2:=e21) (A:=A1).
    refine (jmeq_exist _ _ H).
     apply set_forall_ext. intro. apply ty_eq with (e1:=a;:e11) (e2:=e21) (A:=A1).
     intros. apply forall_ext. intro A5. apply forall_ext. intro A6. apply forall_ext. intro R1.
     rewrite diagonal_app. rewrite diagonal_app. rewrite diagonal_app. simpl.
     apply IHrel_eq with (re1:=R1;;diagonal e11) (re2:=diagonal e21) (R:=@eq A1).
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
     intros. apply forall_ext. intro A5. apply forall_ext. intro A6. apply forall_ext. intro R1.
     rewrite diagonal_app. rewrite diagonal_app. rewrite diagonal_app. simpl.
     apply IHrel_eq with (re1:=R1;;diagonal e12) (re2:=diagonal e22) (R:=@eq A2).
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

Definition ty_sem_shift1 : forall g (e : ty_environment g) ty A,
  ty_sem e ty ->
  ty_sem (A;:e) (shift g 0 ty).
intros. eapply coerce. symmetry. apply ty_shift1_equal. assumption.
Defined.

Lemma ty_rel_shift1_equal : forall g (e1 e2:ty_environment g) (re : rel_environment e1 e2) ty
  (A1 A2 : Set) (R : A1 -> A2 -> Prop) t1 t2 t1' t2',
  JMeq t1 t1' ->
  JMeq t2 t2' ->
  ty_rel re ty t1 t2 = ty_rel (R;;re) (shift1 ty) t1' t2'.
intros.
destruct (shift_sem_rel_eq 0 g ty).
unfold shift1.
apply H2 with (re1:=rel_nil) (R:=R).
 assumption.
 assumption.
Save.

Lemma ty_rel_shift1 : forall g (e1 e2:ty_environment g) re ty A1 A2 t1 t2 R,
  ty_rel re ty t1 t2 ->
  ty_rel (R;;re) (shift1 ty) (ty_sem_shift1 e1 ty A1 t1) (ty_sem_shift1 e2 ty A2 t2).
intros. refine (coerce _ H). symmetry. 
rewrite <- ty_rel_shift1_equal with (t1:=t1) (t2:=t2) (t1':=ty_sem_shift1 e1 ty A1 t1) (t2':=ty_sem_shift1 e2 ty A2 t2).
 reflexivity.
 symmetry. apply coerce_jmeq.
 symmetry. apply coerce_jmeq.
Save.
