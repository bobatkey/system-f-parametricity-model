Require Import List.
Require Import Arith.
Require Import Program.

Require Import Axioms.
Require Import TypeSyntax.
Require Import TypeSystem.
Require Import KripkeSemantics.
Require Import KripkeShifting.
Require Import KripkeSubstitution.

Set Implicit Arguments.

(********************************************************************************)
Fixpoint context_sem g (e:ty_environment g) (ctxt:context g) : Set :=
  match ctxt with
    | nil => unit
    | cons a ctxt => (context_sem e ctxt * ty_sem e a)%type
  end.

Definition lookup_ctxt : forall g i (ctxt:context g) ty, In i ctxt ty -> forall e, context_sem e ctxt -> ty_sem e ty.
intros g i ctxt ty i0. induction i0; intros.
 destruct H. apply t.
 destruct H. apply IHi0. apply c.
Defined.

Definition context_rel : forall g W (Worder:preorder W)
  (e1 e2 : ty_environment g) ctxt,
  rel_environment Worder e1 e2 -> W -> context_sem e1 ctxt -> context_sem e2 ctxt -> Prop.
intros g W Worder e1 e2 ctxt re w.
induction ctxt.
 exact (fun _ _ => True).
 intros [g1 a1] [g2 a2]. apply and.
  apply (IHctxt g1 g2).
  apply (ty_rel re a w a1 a2).
Defined.

Lemma context_rel_kripke : forall g W (Worder:preorder W) (e1 e2 : ty_environment g) (ctxt : context g) (re : rel_environment Worder e1 e2),
  kripke_relation Worder (context_rel (Worder:=Worder) ctxt re).
intros. unfold kripke_relation. intros. induction ctxt.
 simpl in *. trivial.
 simpl in *. destruct a as [g1 a1]. destruct b as [g2 a2]. destruct H0 as [g1_g2 a1_a2]. split.
  apply IHctxt. assumption.
  refine (heredity _ _ _ _ _ _ _ _). eassumption. assumption.
Save.

Lemma lookup_ctxt_rel : forall g W (Worder:preorder W) i ctxt ty
  (e1 e2 : ty_environment g)
  (re : rel_environment Worder e1 e2)
  (g1 : context_sem e1 ctxt)
  (g2 : context_sem e2 ctxt)
  (i0 : In i ctxt ty)
  (w  : W),
  context_rel ctxt re w g1 g2 ->
  ty_rel re ty w (lookup_ctxt i0 e1 g1) (lookup_ctxt i0 e2 g2).
induction i0; intros; simpl in *.
 destruct g1 as [g1 x1]. destruct g2 as [g2 x2]. destruct H. apply H0.
 destruct g1 as [g1 x1]. destruct g2 as [g2 x2]. apply IHi0. destruct H. apply H.
Defined.

Definition context_sem_shift1 : forall g (e : ty_environment g) ctxt A,
  context_sem e ctxt ->
  context_sem (A;:e) (context_shift1 ctxt).
induction ctxt; intros.
 simpl. trivial.
 simpl in *. destruct H. split.
  apply IHctxt. apply c.
  apply ty_sem_shift1. apply t.
Defined.

Definition context_rel_shift1 : forall g W (Worder:preorder W) (e1 e2:ty_environment g) re ctxt A1 A2
  R (Rkripke:kripke_relation Worder R) g1 g2 (w:W),
  context_rel (Worder:=Worder) ctxt re w g1 g2 ->
  context_rel (context_shift1 ctxt) (Rkripke;;re) w (context_sem_shift1 e1 ctxt A1 g1) (context_sem_shift1 e2 ctxt A2 g2).
induction ctxt; intros.
 simpl. trivial.
 simpl in *. destruct g1. destruct g2. destruct H. split.
  apply IHctxt. apply H.
  apply ty_rel_shift1. apply H0.
Defined.

Lemma context_rel_diagonal : forall g W (Worder:preorder W) (e:ty_environment g) ctxt s w,
  context_rel ctxt (diagonal Worder e) w s s.
intros g W Worder e ctxt s w. induction ctxt.
 simpl. trivial.
 simpl. destruct s. split.
  apply IHctxt.
  rewrite rel_diagonal. reflexivity.
Save.

Definition term_sem : forall g ctxt ty,
  term ctxt ty ->
  { x : forall (e : ty_environment g), context_sem e ctxt -> ty_sem e ty
    | forall W (Worder:preorder W)
             (e1 e2 : ty_environment g) (re : rel_environment Worder e1 e2)
             (g1:context_sem e1 ctxt) (g2:context_sem e2 ctxt) w,
      context_rel ctxt re w g1 g2 -> ty_rel re ty w (x e1 g1) (x e2 g2) }.
intros g ctxt ty tm.
induction tm.
 (* t_var *)
 exists (lookup_ctxt i0).
 auto using lookup_ctxt_rel.
 (* t_app *)
 destruct IHtm1 as [tm1_sem tm1_rel].
 destruct IHtm2 as [tm2_sem tm2_rel].
 exists (fun e s => tm1_sem e s (tm2_sem e s)).
 intros. apply tm1_rel with (w:=w). apply H. apply (preorder_refl Worder). apply tm2_rel. apply H.
 (* t_abs *)
 destruct IHtm as [tm_sem tm_rel].
 exists (fun e s x => tm_sem e (s,x)).
 unfold ty_rel. simpl. intros.
 simpl. apply tm_rel. simpl. split.
  refine (context_rel_kripke _ _ _ _ _ _ _ _). eassumption. assumption.
  assumption.
 (* t_tyabs *)
 destruct IHtm as [tm_sem tm_rel].
 unfold ty_sem. simpl.
 unfold ty_rel in tm_rel. 
 exists (fun e s =>
          exist (fun x => forall W (Worder:preorder W) (A1 A2 : Set) (R : W -> A1 -> A2 -> Prop)
                                 (Rkripke : kripke_relation Worder R) w,
                                 projT2 (ty_sem_rel ty) W Worder (A1;:e) (A2;:e) (Rkripke;;diagonal Worder e) w (x A1) (x A2))
                (fun A => tm_sem (A;:e) (context_sem_shift1 e ctxt A s))
                (fun W Worder A1 A2 R Rkripke w =>
                    tm_rel W Worder (A1;:e) (A2;:e) (Rkripke;;diagonal Worder e)
                                (context_sem_shift1 e ctxt A1 s) (context_sem_shift1 e ctxt A2 s) w
                                (context_rel_shift1 (diagonal Worder e) ctxt Rkripke s s w (context_rel_diagonal Worder e ctxt s w)))).
 unfold ty_rel. simpl.
 intros. apply tm_rel. apply context_rel_shift1. assumption.
 (* t_tyapp *)
 destruct IHtm as [tm_sem tm_rel].
 unfold ty_sem in tm_sem. unfold ty_rel in *. simpl in *.
 exists (fun e s => type_subst1_sem ty1 ty2 e (projT1 (tm_sem e s) (ty_sem e ty2))).
 intros. apply type_subst1_rel. apply tm_rel. assumption.
Defined.
