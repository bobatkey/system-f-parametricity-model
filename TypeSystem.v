Require Import List.
Require Import Arith.
Require Import Program.

Require Import Axioms.
Require Import TypeSyntax.

Set Implicit Arguments.

Definition context := fun g => list (type g).

Inductive In (A:Set) : nat -> list A -> A -> Set :=
| in_cons1 : forall x l,
  In 0 (cons x l) x
| in_cons2 : forall n l x y,
  In n l x ->
  In (S n) (cons y l) x.

Definition context_shift1 : forall g, context g -> context (S g) :=
 fun g ctxt => map (@shift1 g) ctxt.

Inductive term : forall g, context g -> type g -> Set :=
| t_var : forall g (ctxt:context g) i ty,
  In i ctxt ty ->
  term ctxt ty

| t_app : forall g (ctxt:context g) ty1 ty2,
  term ctxt (ty_arr ty1 ty2) ->
  term ctxt ty1 ->
  term ctxt ty2

| t_abs : forall g (ctxt:context g) ty1 ty2,
  term (ty1::ctxt) ty2 ->
  term ctxt (ty_arr ty1 ty2)

| t_tyabs : forall g (ctxt:context g) ty,
  term (context_shift1 ctxt) ty ->
  term ctxt (ty_forall ty)

| t_tyapp : forall g (ctxt:context g) ty1 ty2,
  term ctxt (ty_forall ty1) ->
  term ctxt (type_subst1 ty1 ty2).

