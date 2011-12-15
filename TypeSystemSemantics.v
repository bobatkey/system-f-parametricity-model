Require Import List.
Require Import Arith.
Require Import Program.

Require Import Axioms.
Require Import TypeSyntax.
Require Import Semantics.
Require Import Shifting.
Require Import Substitution.
Require Import TypeSystem.

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

Definition context_rel : forall g (e1 e2 : ty_environment g) ctxt, rel_environment e1 e2 -> context_sem e1 ctxt -> context_sem e2 ctxt -> Prop.
intros g e1 e2 ctxt re.
induction ctxt.
 exact (fun _ _ => True).
 intros [g1 a1] [g2 a2]. apply and.
  apply (IHctxt g1 g2).
  apply (ty_rel re a a1 a2).
Defined.

Lemma lookup_ctxt_rel : forall g i ctxt ty
  (e1 e2 : ty_environment g)
  (re : rel_environment e1 e2)
  (g1 : context_sem e1 ctxt)
  (g2 : context_sem e2 ctxt)
  (i0 : In i ctxt ty),
  context_rel ctxt re g1 g2 ->
  ty_rel re ty (lookup_ctxt i0 e1 g1) (lookup_ctxt i0 e2 g2).
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

Definition context_rel_shift1 : forall g (e1 e2:ty_environment g) re ctxt A1 A2 R g1 g2,
  context_rel ctxt re g1 g2 ->
  context_rel (context_shift1 ctxt) (R;;re) (context_sem_shift1 e1 ctxt A1 g1) (context_sem_shift1 e2 ctxt A2 g2).
induction ctxt; intros.
 simpl. trivial.
 simpl in *. destruct g1. destruct g2. destruct H. split.
  apply IHctxt. apply H.
  apply ty_rel_shift1. apply H0.
Defined.

Lemma context_rel_diagonal : forall g (e:ty_environment g) ctxt s,
  context_rel ctxt (diagonal e) s s.
intros g e ctxt s. induction ctxt.
 simpl. trivial.
 simpl. destruct s. split.
  apply IHctxt.
  rewrite rel_diagonal. reflexivity.
Save.

Definition term_sem : forall g ctxt ty,
  term ctxt ty ->
  { x : forall (e : ty_environment g), context_sem e ctxt -> ty_sem e ty
    | forall (e1 e2 : ty_environment g) (re : rel_environment e1 e2)
             (g1:context_sem e1 ctxt) (g2:context_sem e2 ctxt),
      context_rel ctxt re g1 g2 -> ty_rel re ty (x e1 g1) (x e2 g2) }.
intros g ctxt ty tm.
induction tm.
 (* t_var *)
 exists (lookup_ctxt i0).
 auto using lookup_ctxt_rel.
 (* t_app *)
 destruct IHtm1 as [tm1_sem tm1_rel].
 destruct IHtm2 as [tm2_sem tm2_rel].
 exists (fun e s => tm1_sem e s (tm2_sem e s)).
 intros. apply tm1_rel. apply H. apply tm2_rel. apply H.
 (* t_abs *)
 destruct IHtm as [tm_sem tm_rel].
 exists (fun e s x => tm_sem e (s,x)).
 unfold ty_rel. simpl. intros.
 simpl. apply tm_rel. simpl. split; assumption.
 (* t_tyabs *)
 destruct IHtm as [tm_sem tm_rel].
 unfold ty_sem. simpl.
 unfold ty_rel in tm_rel. 
 exists (fun e s =>
          exist (fun x => forall (A1 A2 : Set) (R : A1 -> A2 -> Prop), ty_rel (R;;diagonal e) ty (x A1) (x A2))
                (fun A => tm_sem (A;:e) (context_sem_shift1 e ctxt A s))
                (fun A1 A2 R => tm_rel (A1;:e) (A2;:e) (R;;diagonal e)
                                       (context_sem_shift1 e ctxt A1 s) (context_sem_shift1 e ctxt A2 s) 
                                       (context_rel_shift1 (diagonal e) ctxt R s s (context_rel_diagonal e ctxt s)))).
 unfold ty_rel. simpl.
 intros. apply tm_rel. apply context_rel_shift1. assumption.
 (* t_tyapp *)
 destruct IHtm as [tm_sem tm_rel].
 unfold ty_sem in tm_sem. unfold ty_rel in *. simpl in *.
 exists (fun e s => type_subst1_sem ty1 ty2 e (projT1 (tm_sem e s) (ty_sem e ty2))).
 intros. apply type_subst1_rel. apply tm_rel. assumption.
Defined.
