Require Import List.
Require Import Arith.
Require Import Omega.

Require Import Axioms.
Require Import TypeSyntax.
Require Import KripkeSemantics.

Set Implicit Arguments.

Definition hoas : type O.
apply ty_forall.
apply ty_arr. 
 apply ty_arr.
  apply ty_arr.
   apply ty_var. apply var with (i:=0). constructor.
   apply ty_var. apply var with (i:=0). constructor.
  apply ty_var. apply var with (i:=0). constructor.
 apply ty_arr.
  apply ty_arr.
   apply ty_var. apply var with (i:=0). constructor.
   apply ty_arr.
    apply ty_var. apply var with (i:=0). constructor.
    apply ty_var. apply var with (i:=0). constructor.
  apply ty_var. apply var with (i:=0). constructor.
Defined.

Inductive pre_term : Set :=
| preVar : nat -> pre_term
| preLam : pre_term -> pre_term
| preApp : pre_term -> pre_term -> pre_term.

Inductive wf_term : nat -> pre_term -> Prop :=
| wf_var : forall g i, i < g -> wf_term g (preVar i)
| wf_lam : forall g t, wf_term (S g) t -> wf_term g (preLam t)
| wf_app : forall g t1 t2, wf_term g t1 -> wf_term g t2 -> wf_term g (preApp t1 t2).

Inductive term : nat -> Set :=
| Var : forall g i, i < g -> term g
| Lam : forall g, term (S g) -> term g
| App : forall g, term g -> term g -> term g.

Definition wf_to_term : forall t g, wf_term g t -> term g.
induction t; intros.
 (* preVar *)
 apply Var with (i:=n). inversion H. assumption.
 (* preLam *)
 apply Lam. apply IHt. inversion H. assumption.
 (* preApp *)
 apply App.
  apply IHt1. inversion H. assumption.
  apply IHt2. inversion H. assumption.
Defined.

Definition term_to_wf : forall g, term g -> { t : pre_term | wf_term g t }.
intros. induction H.
 exists (preVar i). apply wf_var. assumption.
 exists (preLam (proj1_sig IHterm)). apply wf_lam. apply (proj2_sig IHterm).
 exists (preApp (proj1_sig IHterm1) (proj1_sig IHterm2)). apply wf_app.
  apply (proj2_sig IHterm1).
  apply (proj2_sig IHterm2).
Defined.

Lemma term_wf_iso1 : forall g (t:term g), wf_to_term (proj2_sig (term_to_wf t)) = t.
intros. induction t; simpl.
 (* Var *)
 reflexivity.
 (* Lam *)
 apply f_equal. apply IHt.
 (* App *)
 apply f_equal2; assumption.
Save.

Lemma term_wf_iso2 : forall g t (wf:wf_term g t), proj1_sig (term_to_wf (wf_to_term wf)) = t.
intros g t. revert g. induction t; intros; simpl.
 (* preVar *)
 reflexivity.
 (* preLam *)
 apply f_equal. apply IHt.
 (* preApp *)
 apply f_equal2. apply IHt1. apply IHt2.
Save.

Definition to_pre_term : nat -> ty_sem ty_nil hoas -> pre_term.
unfold ty_sem. simpl.
intros g [cterm _].
apply (cterm (nat -> pre_term)).
 exact (fun f   i => preLam (f (fun j => preVar (j - (S i))) (S i))).
 exact (fun x y i => preApp (x i) (y i)).
 exact g.
Defined.

Definition natorder : preorder nat.
apply mkPorder with (preorder_order:=le).
 apply le_refl.
 apply le_trans.
Defined.

Lemma to_pre_term_wf : forall t g, wf_term g (to_pre_term g t).
unfold ty_sem. unfold to_pre_term. simpl.
intros [t P] g.

refine (P nat natorder
          (nat -> pre_term) unit
          (fun w x y => forall w', natorder w w' -> wf_term w' (x w'))
          _
          g g
          (fun f i => preLam (f (fun j => preVar (j - (S i))) (S i)))
          (fun f   => tt)
          _ _
          g
          (fun x y i => preApp (x i) (y i))
          (fun x y   => tt)
          _ _
          _ _).

(* R is a kripke relation *)
unfold kripke_relation. intros. apply H0. eapply le_trans. apply H. apply H1.

(* g <= g *)
apply le_refl.

(* the lam case preserves the relation *)
clear P. intros. 
apply wf_lam. 
apply H0 with (w'0:=S w'0).
 apply tt.
 apply le_S. apply H1.
 intros. apply wf_var.
  apply lt_minus.
   apply H2.
   unfold lt. apply le_n_S. apply le_O_n.
 apply le_refl.

(* g <= g *)
apply le_refl.

(* app case preserves the order *)
clear P. intros. 
apply wf_app.
 apply H0. eapply le_trans; eassumption.
 apply H2. apply H3.

(* g <= g *)
apply le_refl.
Defined.

Definition to_term : forall g, ty_sem ty_nil hoas -> term g.
intros g t.
apply wf_to_term with (t:=to_pre_term g t).
apply to_pre_term_wf.
Defined.

Inductive vec (A:Set) : nat -> Set :=
| vec_nil  : vec A 0
| vec_cons : forall n, A -> vec A n -> vec A (S n).

Definition idx : forall A n i, i < n -> vec A n -> A.
fix 3. intros. destruct i.
 destruct H0.
  elimtype False. inversion H.
  apply a.
 destruct H0.
  elimtype False. inversion H.
  apply idx with (n:=n) (i:=i).
   apply lt_S_n. assumption.
   assumption.
Defined.

Definition from_term : term 0 -> ty_sem ty_nil hoas.
unfold ty_sem. unfold hoas. simpl.
intros t.
exists (fun A lam app =>
         @term_rec (fun n t => vec A n -> A)
                   (fun g i l env => idx l env)
                   (fun g _ f env => lam (fun x => f (vec_cons x env)))
                   (fun g _ x _ y env => app (x env) (y env))
                   0 t (vec_nil A)).

intros.
set (w2:=w'0).
assert (Worder w'0 w2). apply (preorder_refl Worder). 
assert (forall i (l:i<0) w, Worder w2 w -> R w (idx l (vec_nil A1)) (idx l (vec_nil A2))).
 intros. inversion l.
generalize w2 H3 H4. clear w2 H3 H4.
generalize (vec_nil A1).
generalize (vec_nil A2).
generalize t. clear t.
generalize 0.

induction t; intros.
 (* Var *)
 simpl. apply H4. apply (preorder_refl Worder).
 (* Lam *)
 simpl. apply H0.
  eapply (preorder_trans Worder); eassumption.
  intros. apply IHt. 
   eapply (preorder_trans Worder); eassumption.
   intros. destruct i.
    simpl. unfold kripke_relation in Rkripke. apply Rkripke with (x:=w'1). assumption. assumption.
    simpl. apply H4.
     eapply (preorder_trans Worder); eassumption.
 (* App *)
 simpl. apply H2 with (w':=w2).
  assumption.
  apply IHt1; assumption.
  apply (preorder_refl Worder).
  apply IHt2; assumption.
Defined.

Lemma hoas_iso1aux : forall t (wf:wf_term 0 t),
 to_pre_term 0 (from_term (wf_to_term wf)) = t.
unfold to_pre_term.
unfold from_term.

intro t.

assert (forall i (l:i<0) n', 0 <= n' -> idx l (vec_nil (nat -> pre_term)) n' = preVar (i + (n' - 0))).
 intros. inversion l.
revert H.
generalize (vec_nil (nat -> pre_term)).
generalize 0.

induction t; intros.
 (* preVar *)
 simpl. 
 match goal with [ |- idx ?X _ _ = _ ] => set (x:=X) end. revert x. intros.
 pose (H0:=H n x n0). rewrite <- minus_n_n in H0. rewrite <- plus_n_O in H0. apply H0. apply le_refl. 
 (* preLam *)
 simpl. apply f_equal. apply IHt.
 intros. destruct i.
  simpl. reflexivity.
  simpl. rewrite H. apply f_equal. omega. omega.
 (* preApp *)
 simpl. apply f_equal2.
  apply IHt1. assumption.
  apply IHt2. assumption.
Save.

Lemma hoas_iso1 : forall t, to_term 0 (from_term t) = t.
intros. unfold to_term.
replace t with (wf_to_term (proj2_sig (term_to_wf t))) by apply term_wf_iso1.
match goal with [ |- @wf_to_term _ _ ?X = _ ] => set (p:=X) end. generalize p. clear p. intro.
match goal with [ |- @wf_to_term (to_pre_term 0 (from_term (wf_to_term ?X))) _ _ = _ ] => set (p1:=X) in * end. 

assert (to_pre_term 0 (from_term (@wf_to_term (proj1_sig (term_to_wf t)) 0 p1))=proj1_sig (term_to_wf t))
    by apply hoas_iso1aux. 
revert p. rewrite H. intro p.

replace p with p1 by apply proof_irrelevance.
reflexivity.
Save.

Definition list_to_vec : forall (A:Set) (l:list A), vec A (length l).
intros. induction l.
 apply vec_nil.
 apply (vec_cons a IHl).
Defined.

Lemma lookup_prop : forall A (b c:list A) x,
  nth_error (c ++ x::b) (length (c ++ x::b) - S (length b)) = Some x.
intros. induction c.
 simpl. rewrite <- minus_n_n. simpl. reflexivity.
 replace (length ((a::c) ++ x :: b) - S (length b)) with (S (length (c ++ x::b) - S (length b))).
 simpl. apply IHc.
 simpl. rewrite app_length. simpl. omega.
Save.

Lemma lookup_idx : forall (A:Set) (l:list A) i (p:i<length l) x,
  nth_error l i = Some x ->
  idx p (list_to_vec l) = x.
intros A l. induction l.
 intros. inversion p.
 intros. simpl. destruct i.
  simpl in *. inversion H. reflexivity.
  simpl in *. apply IHl. apply H.
Save.

(* prefix ordering *)
Definition listorder : forall (A:Set), preorder (list A).
intro A.
apply mkPorder with (preorder_order:=fun x y => exists z, y = z ++ x).
 intros. exists nil. reflexivity.
 intros. destruct H. destruct H0. rewrite H in H0. exists (x1 ++ x0). rewrite app_ass. assumption.
Defined.

Lemma hoas_iso2 : forall t, from_term (to_term 0 t) = t.
unfold ty_sem. unfold from_term. unfold to_term. intros. 
match goal with [ |- ?x = ?y ] => refine (sig_eq x y _) end. simpl in *. destruct t as [t P]. simpl in *.
ext A. ext lam. ext appl.

match goal with [ |- term_rec _ _ _ _ (wf_to_term ?X) _ = _ ] => set (p:=X) end. generalize p. clear p.
change (vec_nil A) with (list_to_vec (@nil A)).
change 0 with (length (@nil A)).
intros.

refine (P (list A) (listorder A) (nat -> pre_term) A
          (fun env x y =>
             forall env', listorder A env env' ->
             forall p0, term_rec (fun n _ => vec A n -> A)
                                 (fun g i (l:i < g) env => idx l env)
                                 (fun g _ f env => lam (fun x => f (vec_cons x env)))
                                 (fun g _ x _ y env => appl (x env) (y env))
                                 (@wf_to_term (x (length env')) (length env') p0) (list_to_vec env') = y)
          _ (@nil A)
          (@nil A) _ _ _
          _
          (@nil A) _ _ _
          _
          _ _ _); clear P; clear p.

(* R is a kripke relation *)
unfold kripke_relation. intros. apply H0. eapply (preorder_trans (listorder A)); eassumption.

(* [] <= [] *)
apply (preorder_refl (listorder A)).

(* lam case *)
intros. simpl.
apply f_equal.
ext x. 
change (vec_cons x (list_to_vec env')) with (list_to_vec (x::env')).
change (S (length env')) with (length (x::env')).
apply H0 with (w'0:=x::env').
 eapply (preorder_trans (listorder A)).
  apply H1.
  unfold listorder. simpl. exists (x::nil). reflexivity.
 intros. simpl. apply lookup_idx. destruct H2. subst env'0. apply lookup_prop.
 apply (preorder_refl (listorder A)).

(* [] <= [] *)
apply (preorder_refl (listorder A)).

(* app case *)
intros. simpl. 
apply f_equal2.
 (* first two arguments are related *)
 apply H0. eapply (preorder_trans (listorder A)); eassumption.
 (* second two arguments are related *)
 apply H2. assumption.

(* [] <= [] *)
apply (preorder_refl (listorder A)).
Save.
