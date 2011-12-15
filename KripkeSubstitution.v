Require Import List.
Require Import Arith.
Require Import Program.

Require Import Axioms.
Require Import JMUtils.
Require Import TypeSyntax.
Require Import KripkeSemantics.
Require Import KripkeShifting.

Set Implicit Arguments.


Definition subst_lookup_var_eq : forall i g1 g2 ty1 (l : i < g1 + 1 + g2),
  forall (e1 : ty_environment g1) (e2 : ty_environment g2),
     ty_sem (app e1 e2) (subst_var g2 g1 (var l) (refl_equal (g1 + 1 + g2)) ty1) =
     lookup_var (var l) (app (app e1 (ty_sem (app e1 e2) ty1;: ty_nil)) e2).
intros. 
unfold ty_sem in *.
simpl in *. unfold eq_rec_r in *. simpl.
revert ty1.
destruct (lt_eq_lt_dec i g1) as [[X|X]|X]; simpl.
 (* i < g1 *)
 generalize (app e1 e2) at 2 as e3. 
 generalize (lt_plus_trans i g1 g2 X).
 intros. set (Y:=lookup l0 (app e1 e2)). revert ty1 e3. generalize (g1 + g2) as g3.
 unfold Y. clear Y.
 revert g1 g2 l e1 e2 X l0. induction i; intros.
  (* i = 0 *)
  destruct e1.
   (* e1 = ty_nil *)
   elimtype False. inversion X.
   (* e1 = ty_cons *)
   simpl in *. reflexivity.
  (* i > 0 *)
  destruct e1.
   (* e1 = ty_nil *)
   elimtype False. inversion X.
   (* e1 = ty_cons ... *)
   simpl. fold plus. eapply IHi.
    apply lt_S_n. assumption.
 (* i = g1 *)
 generalize (app e1 e2) as e3. 
 generalize (g1 + g2) as g3.
 intros.
 revert g1 g2 l e1 e2 X. induction i; intros.
  (* i = 0 *)
  destruct e1.
   (* e1 = ty_nil *)
   simpl in *. reflexivity.
   (* e1 = ty_cons *)
   elimtype False. inversion X.
  (* i > 0 *)
  destruct e1.
   (* e1 = ty_nil *)
   elimtype False. inversion X.
   (* e1 = ty_cons *)
   simpl in *. fold plus. apply IHi.
    inversion X. reflexivity.
 (* g1 < i *)
 destruct (O_or_S i) as [[i' i'_Si]|i_0].
  (* i = S i' *)
  simpl in *. 
  intros.  match goal with [|-lookup ?X _ = _] => generalize X end. intros.
  set (Y:=lookup l0 (app e1 e2)).
  revert ty1. generalize (app e1 e2) as e3. generalize (g1 + g2) as g3.
  intros. unfold Y. clear Y.
  revert g1 g2 l e1 e2 X l0. subst i. induction i'; intros.
   (* i' = 0 *)
   destruct e1.
    (* e1 = ty_nil *)
    simpl in *. apply f_equal. apply proof_irrelevance.
    (* e1 = ty_cons *)
    elimtype False. inversion X. inversion H0.
   (* i' > 0 *)
   destruct e1.
    (* e1 = ty_nil *)
    simpl in *. apply f_equal. apply proof_irrelevance.
    (* e1 = ty_cons *)
    simpl app. simpl lookup. fold plus.
    eapply IHi' with (l:=lt_S_n (S i') (i + 1 + g2) l). 
     apply lt_S_n. assumption.
  (* i = 0 *)
  elimtype False. subst i. inversion X.
Save.

Lemma subst_lookup_var_rel : forall W (Worder:preorder W) i g1 g2 ty1 (l:i < g1 + 1 + g2)
  (e11 e12 : ty_environment g1) (e21 e22 : ty_environment g2)
  (re1 : rel_environment Worder e11 e12) (re2 : rel_environment Worder e21 e22)
  (Rkripke : kripke_relation Worder (fun (w  : W)
                 (x  : projT1 (ty_sem_rel ty1) (app e11 e21))
                 (y : projT1 (ty_sem_rel ty1) (app e12 e22)) =>
             projT2 (ty_sem_rel ty1) W Worder
               (app e11 e21) 
               (app e12 e22) (re_app re1 re2) w x y))
  t1 t2 t1' t2' w,
  JMeq t1 t1' ->
  JMeq t2 t2' ->
  ty_rel (re_app re1 re2) (subst_var g2 g1 (var l) (refl_equal (g1 + 1 + g2)) ty1) w t1 t2 =
  rel_lookup_var (var l)
     (re_app
        (re_app re1
           (Rkripke;; rel_nil Worder)) re2) w t1' t2'.
intros.
unfold ty_rel in *. unfold ty_sem in *. simpl in *. unfold eq_rec_r in *. simpl.
destruct (lt_eq_lt_dec i g1) as [[X|X]|X]; simpl in *.
 (* i < g1 *)
 revert t1 t2 H H0. generalize (lt_plus_trans i g1 g2 X). intros.
 revert t1' t2' H H0 Rkripke. 
 set (Y := rel_lookup l0 (re_app re1 re2) w t1 t2). 
 set (Y1:=lookup l0 (app e11 e21)). set (Y2:=lookup l0 (app e12 e22)).
 generalize (re_app re1 re2) as re3.
 generalize (app e11 e21) as e31. generalize (app e12 e22) as g32.
 revert ty1. generalize (g1+g2) as g3.
 unfold Y. unfold Y1. unfold Y2. clear Y Y1 Y2.
 intros.
 revert g1 g2 l e11 e12 e21 e22 re1 re2 X l0 t1 t2 t1' t2' H0 H. induction i; intros.
  (* i = 0 *)
  destruct re1.
   (* e1 = ty_nil *)
   elimtype False. inversion X.
   (* e1 = ty_cons *)
   simpl in *. apply f_jmequal2. reflexivity. assumption. assumption.
  (* i > 0 *)
  destruct re1.
   (* e1 = ty_nil *)
   elimtype False. inversion X.
   (* e1 = ty_cons ... *)
   simpl. fold plus. apply IHi with (re1:=re1) (re2:=re2).
    apply lt_S_n. assumption.
    assumption.
    assumption.
 (* i = g1 *)
 revert ty1 t1 t2 t1' t2' H H0 Rkripke. 
 generalize (re_app re1 re2) as re3. 
 generalize (app e11 e21) as e31.
 generalize (app e12 e22) as e32.
 generalize (g1 + g2) as g3.
 intros.
 revert g1 g2 l e11 e12 e21 e22 re1 re2 t1 t2 t1' t2' H0 H X. induction i; intros.
  (* i = 0 *)
  destruct re1.
   (* e1 = ty_nil *)
   simpl in *. rewrite H0. rewrite H. reflexivity.
   (* e1 = ty_cons *)
   elimtype False. inversion X.
  (* i > 0 *)
  destruct re1.
   (* e1 = ty_nil *)
   elimtype False. inversion X.
   (* e1 = ty_cons *)
   simpl in *. fold plus in *. apply IHi with (re1:=re1) (re2:=re2).
    assumption.
    assumption.
    inversion X. reflexivity.
 (* g1 < i *)
 destruct (O_or_S i) as [[i' i'_Si]|i_0].
  (* i = S i' *)
  simpl in *. 
  revert t1 t2 H H0. match goal with [|-forall (_ : lookup ?X _), _ ] => generalize X end. intros.
  revert ty1 t1' t2' H H0 Rkripke.
  set (Y:=rel_lookup l0 (re_app re1 re2) w t1 t2). 
  set (Y1:=lookup l0 (app e11 e21)). set (Y2:=lookup l0 (app e12 e22)).
  generalize (re_app re1 re2) as re3.
  generalize (app e11 e21) as e31.
  generalize (app e12 e22) as e32.
  generalize (g1 + g2) as g3.
  unfold Y. unfold Y1. unfold Y2. clear Y Y1 Y2.
  intros.
  subst i.
  revert g1 g2 l0 l e11 e12 e21 e22 re1 re2 t1 t2 t1' t2' H H0 X.
  induction i'; intros.
   (* i' = 0 *)
   destruct re1.
    (* e1 = ty_nil *)
    simpl in l0,l.
    assert (lt_S_n 0 g2 l=l0) by apply proof_irrelevance.
    simpl. apply f_jmequal2. 
     rewrite H1. reflexivity.
     assumption.
     assumption.
    (* e1 = ty_cons *)
    elimtype False. inversion X. inversion H2.
   (* i' > 0 *)
   destruct re1.
    (* e1 = ty_nil *)
    simpl in *.
    assert (lt_S_n (S i') g2 l=l0) by apply proof_irrelevance.
    apply f_jmequal2.
     rewrite H1. reflexivity.
     assumption.
     assumption.
    (* e1 = ty_cons *)
    simpl re_app. simpl rel_lookup. fold plus.
    eapply IHi' with (l:=lt_S_n (S i') (n + 1 + g2) l) (re1:=re1) (re2:=re2). 
     assumption.
     assumption.
     apply lt_S_n. assumption.
  (* i = 0 *)
  elimtype False. clear t1 t2 t1' t2' H H0. subst i. inversion X.
Save.

(****************************************)

Lemma ty_env_eq : forall g1 g2 ty (e1 : ty_environment g1) (e2 : ty_environment g2) (A A':Set),
  A = A' ->
  ty_sem (app (app e1 (A;:ty_nil)) e2) ty = ty_sem (app (app e1 (A';:ty_nil)) e2) ty.
intros. subst. reflexivity.
Save.

Lemma rel_env_eq : forall W (Worder:preorder W) g1 g2 ty (e11 e21 : ty_environment g1) (e12 e22 : ty_environment g2)
  (re1 : rel_environment Worder e11 e21) (re2 : rel_environment Worder e12 e22) (A1 A1' A2 A2':Set)
  (R : W -> A1 -> A2 -> Prop) (R' : W -> A1' -> A2' -> Prop)
  (Rkripke : kripke_relation Worder R) (R'kripke : kripke_relation Worder R')
  t1 t2
  t1' t2' w,
  A1 = A1' ->
  A2 = A2' ->
  (forall t1 t2 t1' t2' w, JMeq t1 t1' -> JMeq t2 t2' -> R w t1 t2 = R' w t1' t2') ->
  JMeq t1 t1' ->
  JMeq t2 t2' ->
  ty_rel (re_app (re_app re1 (Rkripke;;rel_nil Worder)) re2) ty w t1 t2 =
  ty_rel (re_app (re_app re1 (R'kripke;;rel_nil Worder)) re2) ty w t1' t2'.
intros. subst.
assert (R=R'). ext w'. ext x. ext y. apply H1; reflexivity.
subst R. assert (Rkripke = R'kripke). apply proof_irrelevance.
rewrite H. rewrite H2. rewrite H3. reflexivity.
Save.

(********************************************************************************)

Ltac fold_ty_sem :=
  match goal with
    [|-context [ projT1 (ty_sem_rel ?TY) ?E ] ] => change (projT1 (ty_sem_rel TY) E) with (ty_sem E TY)
  end.

Definition subst_sem_rel : forall g1 g2 ty1 ty2,
  (forall (e1 : ty_environment g1) (e2 : ty_environment g2),
         ty_sem (app e1 e2) (subst g2 g1 ty1 ty2) = ty_sem (app (app e1 (ty_sem (app e1 e2) ty1;:ty_nil)) e2) ty2)
  /\
  (forall W (Worder : preorder W)
          (e11 e12 : ty_environment g1) (e21 e22 : ty_environment g2)
          (re1 : rel_environment Worder e11 e12) (re2 : rel_environment Worder e21 e22) t1 t2 t1' t2' w,
                  JMeq t1 t1' ->
                  JMeq t2 t2' ->
                  ty_rel (re_app re1 re2) (subst g2 g1 ty1 ty2) w t1 t2 =
                  ty_rel (re_app (re_app re1 (heredity (re_app re1 re2) ty1;;rel_nil Worder)) re2) ty2 w t1' t2').
intros g1 g2 ty1 ty2. revert ty1. dependent induction ty2.
 (* ty_var *)
 unfold ty_rel. unfold ty_sem. simpl. 
 dependent destruction v. split; intros.
  (* types *)
  fold_ty_sem. fold_ty_sem. rewrite <- subst_lookup_var_eq. reflexivity.
  (* relations *)
  rewrite <- subst_lookup_var_rel with (t1:=t1) (t2:=t2); trivial.
 (* ty_arr *)
 intros. 
 change (subst g2 g1 ty1 (ty_arr ty2_1 ty2_2)) with (ty_arr (subst g2 g1 ty1 ty2_1) (subst g2 g1 ty1 ty2_2)).
 unfold ty_rel in *. unfold ty_sem in *. simpl in *.
 destruct (IHty2_1 g1 g2 ty2_1) with (ty1:=ty1) as [ty_eq1 rel_eq1]. reflexivity. reflexivity.
 destruct (IHty2_2 g1 g2 ty2_2) with (ty1:=ty1) as [ty_eq2 rel_eq2]. reflexivity. reflexivity.
 clear IHty2_1 IHty2_2.
 split; intros.
  (* types *)
  rewrite ty_eq1. rewrite ty_eq2. reflexivity.
  (* relations *)
  apply prop_ext. split.
   (* -> *)
   intros.
   rewrite <- rel_eq2 with (t1:=t1 (coerce (ty_eq1 e11 e21) x1))
                           (t2:=t2 (coerce (ty_eq1 e12 e22) x2)).
    apply H1. apply H2. rewrite rel_eq1 with (t1':=x1) (t2':=x2).
     apply H3.
     apply coerce_jmeq.
     apply coerce_jmeq.
    apply f_jmequal. apply ty_eq2. assumption. apply coerce_jmeq.
    apply f_jmequal. apply ty_eq2. assumption. apply coerce_jmeq.
   (* <- *)
   intros.
   rewrite rel_eq2 with (t1':=t1' (coerce (sym_eq (ty_eq1 e11 e21)) x1))
                        (t2':=t2' (coerce (sym_eq (ty_eq1 e12 e22)) x2)).
    apply H1. apply H2. rewrite <- rel_eq1 with (t1:=x1) (t2:=x2).
     apply H3.
     symmetry. apply coerce_jmeq.
     symmetry. apply coerce_jmeq.
    apply f_jmequal. apply ty_eq2. assumption. symmetry. apply coerce_jmeq.
    apply f_jmequal. apply ty_eq2. assumption. symmetry. apply coerce_jmeq.
 (* ty_forall *)
 intros.
 change (subst g2 g1 ty1 (ty_forall ty2)) with (ty_forall (subst g2 (S g1) (shift1 ty1) ty2)).
 destruct (IHty2 (S g1) g2 ty2) with (ty1:=shift1 ty1) as [ty_eq rel_eq]. reflexivity. reflexivity.
 clear IHty2.
 unfold ty_sem in *. unfold ty_rel in *. simpl in *.

 assert (ty_eq':forall (e1 : ty_environment g1) (e2 : ty_environment g2) (A : Set),
                 ty_sem (A;: app e1 e2) (subst g2 (S g1) (shift1 ty1) ty2) =
                 ty_sem (A;: app (app e1 (ty_sem (app e1 e2) ty1;: ty_nil)) e2) ty2).
  intros.
  replace (ty_sem (app e1 e2) ty1) with (ty_sem (A;:app e1 e2) (shift1 ty1)).
   apply (ty_eq (A;:e1) e2). 
   symmetry. apply ty_shift1_equal.
 
 assert (fiddle:forall (e1 : ty_environment g1) (e2 : ty_environment g2) (A : Set),
                  ty_sem (app (app (A;: e1) (ty_sem (A;: app e1 e2) (shift1 ty1);: ty_nil)) e2) ty2
                = ty_sem (app (app (A;: e1) (ty_sem (app e1 e2) ty1;: ty_nil)) e2) ty2).
  intros. symmetry. apply ty_env_eq. apply ty_shift1_equal.

 assert (rel_eq':forall (e1 : ty_environment g1) (e2 : ty_environment g2) a b,
   JMeq a b ->
   (forall W (Worder:preorder W) (A1 A2 : Set) (R : W -> A1 -> A2 -> Prop) (Rkripke:kripke_relation Worder R) w,
    projT2 (ty_sem_rel (subst g2 (S g1) (shift1 ty1) ty2)) 
      W Worder (A1;: app e1 e2) (A2;: app e1 e2) (Rkripke;; diagonal Worder (app e1 e2)) w
      (a A1) (a A2)) =
   (forall W (Worder:preorder W) (A1 A2 : Set) (R : W -> A1 -> A2 -> Prop) (Rkripke:kripke_relation Worder R) w,
    projT2 (ty_sem_rel ty2) W Worder
      (A1;: app (app e1 (projT1 (ty_sem_rel ty1) (app e1 e2);: ty_nil)) e2)
      (A2;: app (app e1 (projT1 (ty_sem_rel ty1) (app e1 e2);: ty_nil)) e2)
      (Rkripke;;
       diagonal Worder
         (app (app e1 (projT1 (ty_sem_rel ty1) (app e1 e2);: ty_nil)) e2))
      w (b A1) (b A2))).
   intros.
   apply forall_ext with (A:=Type). intro W. apply forall_ext. intro Worder.
   apply forall_ext. intro A1. apply forall_ext. intro A2. apply forall_ext. intro R. apply forall_ext. intro Rkripke.
   apply forall_ext. intro w.
   rewrite diagonal_app.
   rewrite rel_eq with (re1:=Rkripke;;diagonal Worder e1) (re2:=diagonal Worder e2)
                       (t1':=coerce (fiddle e1 e2 A1) (b A1))
                       (t2':=coerce (fiddle e1 e2 A2) (b A2)).
   rewrite diagonal_app. rewrite diagonal_app. simpl.
   apply rel_env_eq with
     (ty:=ty2)
     (re1:=Rkripke;;diagonal Worder e1)
     (re2:=diagonal Worder e2)
     (Rkripke :=heredity (Rkripke;; re_app (diagonal Worder e1) (diagonal Worder e2)) (shift1 ty1))
     (R'kripke:=@w_eq_kripke W Worder (ty_sem (app e1 e2) ty1)).
    symmetry. apply ty_shift1_equal.
    symmetry. apply ty_shift1_equal.
    intros. rewrite <- diagonal_app. transitivity (ty_rel (diagonal Worder (app e1 e2)) ty1 w0 t1' t2').
     symmetry. apply rel_shift1_equal.
      symmetry. assumption.
      symmetry. assumption.
     apply prop_ext. apply rel_diagonal.
   apply coerce_jmeq.
   apply coerce_jmeq.
   eapply JMeq_trans. (*transitivity (b A1). *)
    apply f_jmequal_type with (A1:=Set) (A1':=Set) (f:=a) (g:=b) (x1:=A1) (y1:=A1).
     intros. rewrite H0. apply ty_eq'.
     assumption.
     reflexivity.
    symmetry. apply coerce_jmeq.
   eapply JMeq_trans. (*transitivity (b A2).*)
    apply f_jmequal_type with (A1:=Set) (A1':=Set) (f:=a) (g:=b) (x1:=A2) (y1:=A2).
     intros. rewrite H0. apply ty_eq'.
     assumption.
     reflexivity.
    symmetry. apply coerce_jmeq.

 split; intros.
  (* types *)
  apply subset_type_eq.
   (* types *)
   apply set_forall_ext. intro A. apply ty_eq'.
   (* relations *)
   apply rel_eq'.
  (* relations *)
  apply forall_ext. intro A1. apply forall_ext. intro A2. apply forall_ext. intro R. apply forall_ext. intro Rkripke.
  destruct t1 as [t1 t1_para]. destruct t1' as [t1' t1'_para].
  destruct t2 as [t2 t2_para]. destruct t2' as [t2' t2'_para]. simpl in *.
  rewrite rel_eq with (re1:=Rkripke;;re1) (re2:=re2)
                       (t1':=coerce (fiddle e11 e21 A1) (t1' A1))
                       (t2':=coerce (fiddle e12 e22 A2) (t2' A2)).
  apply rel_env_eq with
     (re1:=Rkripke;;re1)
     (re2:=re2)
     (Rkripke  := heredity (re_app (Rkripke;; re1) re2) (shift1 ty1))
     (R'kripke := heredity (re_app re1 re2) ty1)
     (ty :=ty2).
   symmetry. apply ty_shift1_equal.
   symmetry. apply ty_shift1_equal.
   intros. symmetry. apply rel_shift1_equal.
    symmetry. assumption.
    symmetry. assumption.
   apply coerce_jmeq.
   apply coerce_jmeq.
   eapply JMeq_trans. (*transitivity (t1' A1).*)
    apply f_jmequal_type with (A1:=Set) (A1':=Set) (f:=t1) (g:=t1') (x1:=A1) (y1:=A1).
     intros. rewrite H1. apply ty_eq'.
     refine (jmeq_exist _ _ H).
      apply set_forall_ext. intro A'. apply ty_eq' with (e1:=e11) (e2:=e21).
      apply rel_eq'.
     reflexivity.
    symmetry. apply coerce_jmeq.
   eapply JMeq_trans. (*transitivity (t2' A2).*)
    apply f_jmequal_type with (A1:=Set) (A1':=Set) (f:=t2) (g:=t2') (x1:=A2) (y1:=A2).
     intros. rewrite H1. apply ty_eq'.
     refine (jmeq_exist _ _ H0).
      apply set_forall_ext. intro A'. apply ty_eq' with (e1:=e12) (e2:=e22).
      apply rel_eq'.
     reflexivity.
    symmetry. apply coerce_jmeq.
Save.

Definition type_subst1_sem : forall g ty1 ty2 (e:ty_environment g),
  ty_sem (ty_sem e ty2;:e) ty1 -> ty_sem e (type_subst1 ty1 ty2).
intros. refine (coerce _ H). 
destruct (subst_sem_rel 0 g ty2 ty1) as [ty_eq _]. apply (ty_eq ty_nil).
Defined.

Lemma eq_impl : forall (A B:Prop),
  A ->
  B = A ->
  B.
intros. subst. assumption.
Save.

Lemma type_subst1_rel : forall W (Worder:preorder W) g ty1 ty2 (e1 e2:ty_environment g) re
  (x1 : forall A : Set, ty_sem (A;:e1) ty1)
  (x2 : forall A : Set, ty_sem (A;:e2) ty1)
  (w : W),
  ty_rel (heredity (Worder:=Worder) re ty2;;re) ty1 w (x1 (ty_sem e1 ty2)) (x2 (ty_sem e2 ty2)) ->
  ty_rel re (type_subst1 ty1 ty2) w
    (type_subst1_sem ty1 ty2 e1 (x1 (ty_sem e1 ty2)))
    (type_subst1_sem ty1 ty2 e2 (x2 (ty_sem e2 ty2))).
intros.
unfold type_subst1_sem.
unfold type_subst1.
destruct (subst_sem_rel 0 g ty2 ty1) as [ty_eq rel_eq].
match goal with [ |- context [ coerce ?p (x1 _) ] ] => set (p1:=p) end.
match goal with [ |- context [ coerce ?p (x2 _) ] ] => set (p2:=p) end.
change re with (re_app (rel_nil Worder) re).
eapply eq_impl.
 apply H.
 apply rel_eq with (re1:=rel_nil Worder) (re2:=re).
  apply coerce_jmeq.
  apply coerce_jmeq.
Save.
