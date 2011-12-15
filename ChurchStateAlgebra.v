Require Import List.
Require Import Arith.
Require Import Omega.
Require Import Program.

Require Import Axioms.
Require Import JMUtils.
Require Import TypeSyntax.
Require Import KripkeSemantics.
Require Import KripkeShifting.
Require Import ChurchSyntax.

Set Implicit Arguments.

(* forall V. forall M. (A -> M) -> (S -> (V -> M) -> M) -> (V -> (S -> M) -> M) -> (V -> S -> M -> M) -> M *)
Definition stmonad : type 0 -> type 0 -> type 0.
intros A St.
apply ty_forall.
apply ty_forall.
 apply ty_arr.
  (* return *)
  apply ty_arr.
   apply (shift1 (shift1 A)).
   apply ty_var. apply var with (i:=0). constructor. constructor.
  apply ty_arr.
   (* new *)
   apply ty_arr.
    apply (shift1 (shift1 St)).
    apply ty_arr.
     apply ty_arr.
      apply ty_var. apply var with (i:=1). constructor.
      apply ty_var. apply var with (i:=0). constructor. constructor.
     apply ty_var. apply var with (i:=0). constructor. constructor.
   apply ty_arr.
    (* lookup *)
    apply ty_arr.
     apply ty_var. apply var with (i:=1). constructor.
     apply ty_arr.
      apply ty_arr.
       apply (shift1 (shift1 St)).
       apply ty_var. apply var with (i:=0). constructor. constructor.
      apply ty_var. apply var with (i:=0). constructor. constructor.
    apply ty_arr.
     (* update *)
     apply ty_arr.
      apply ty_var. apply var with (i:=1). constructor.
      apply ty_arr.
       apply (shift1 (shift1 St)).
       apply ty_arr.
        apply ty_var. apply var with (i:=0). constructor. constructor.
        apply ty_var. apply var with (i:=0). constructor. constructor.
     (* result *)
     apply ty_var. apply var with (i:=0). constructor. constructor.
Defined.

Inductive pre_state_term (A St:Set) : Set :=
| preStop   : A -> pre_state_term A St
| preNew    : St -> pre_state_term A St -> pre_state_term A St
| preLookup : nat -> (St -> pre_state_term A St) -> pre_state_term A St
| preUpdate : nat -> St -> pre_state_term A St -> pre_state_term A St.

Inductive wf_pre_state_term (A St:Set) : nat -> pre_state_term A St -> Prop :=
| wf_stop   : forall a n, wf_pre_state_term n (preStop St a)
| wf_new    : forall n i t, wf_pre_state_term (S n) t -> wf_pre_state_term n (preNew i t)
| wf_lookup : forall n v f, v < n -> (forall i, wf_pre_state_term n (f i)) -> wf_pre_state_term n (preLookup v f)
| wf_update : forall n v i t, v < n -> wf_pre_state_term n t -> wf_pre_state_term n (preUpdate v i t).

Inductive state_term (A St:Set) : nat -> Set :=
| Stop   : forall n, A -> state_term A St n
| New    : forall n, St -> state_term A St (S n) -> state_term A St n
| Lookup : forall n v, v < n -> (St -> state_term A St n) -> state_term A St n
| Update : forall n v, v < n -> St -> state_term A St n -> state_term A St n.

Definition wf_to_state_term : forall A St (t : pre_state_term A St) g, wf_pre_state_term g t -> state_term A St g.
induction t; intros.
 (* preStop *)
 apply Stop. apply a.
 (* preNew *)
 apply New.
  apply s.
  apply IHt. inversion H. assumption.
 (* preLookup *)
 apply Lookup with (v:=n).
  inversion H0. assumption.
  intros. apply H with (s:=H1). inversion H0. apply H6.
 (* preUpdate *)
 apply Update with (v:=n). 
  inversion H. assumption.
  apply s.
  apply IHt. inversion H. assumption.
Defined.

Definition state_term_to_wf : forall A St g, state_term A St g -> { t : pre_state_term A St | wf_pre_state_term g t }.
intros. induction H.
 (* Stop *)
 exists (preStop St a). apply wf_stop.
 (* New *)
 exists (preNew s (proj1_sig IHstate_term)). apply wf_new. apply (proj2_sig IHstate_term).
 (* Lookup *)
 exists (preLookup v (fun s => proj1_sig (H s))). apply wf_lookup. assumption. intros. apply (proj2_sig (H i)).
 (* Update *)
 exists (preUpdate v s (proj1_sig IHstate_term)). apply wf_update. assumption. apply (proj2_sig IHstate_term).
Defined.

Lemma state_term_wf_iso1 : forall A St g (t:state_term A St g), wf_to_state_term (proj2_sig (state_term_to_wf t)) = t.
intros. induction t; simpl.
 (* Stop *)
 reflexivity.
 (* New *)
 rewrite IHt. reflexivity.
 (* Lookup *)
 apply f_equal2.
  reflexivity.
  ext s0. apply H.
 (* Update *)
 rewrite IHt. reflexivity.
Save.

Lemma state_term_wf_iso2 : forall A St (t:pre_state_term A St) g (wf:wf_pre_state_term g t),
  proj1_sig (state_term_to_wf (wf_to_state_term wf)) = t.
induction t; intros; simpl.
 (* preStop *)
 reflexivity.
 (* preNew *)
 apply f_equal. apply IHt.
 (* preLookup *)
 apply f_equal. ext s. apply H.
 (* preUpdate *)
 apply f_equal. apply IHt.
Save.

Definition to_pre_state_term : forall tA tS, ty_sem ty_nil (stmonad tA tS) -> pre_state_term (ty_sem ty_nil tA) (ty_sem ty_nil tS).
intros tA tS.
unfold ty_sem at 1.
unfold stmonad.
intros x. 
simpl in x.
apply ((projT1 (projT1 x (nat -> nat))) (nat -> pre_state_term (ty_sem ty_nil tA) (ty_sem ty_nil tS))).
 (* Stop *)
 refine (fun a i => preStop (ty_sem ty_nil tS) (coerce _ a)).
  apply ty_shift1_twice_equal.
 (* New *)
 refine (fun d f i => preNew (coerce _ d) (f (fun j => j - S i) (S i))).
  apply ty_shift1_twice_equal.
 (* Lookup *)
 refine (fun v f i => preLookup (v i) (fun d => f (coerce _ d) i)).
  symmetry. apply ty_shift1_twice_equal.
 (* Update *)
 refine (fun v d c i => preUpdate (v i) (coerce _ d) (c i)).
  apply ty_shift1_twice_equal.
 (* the final var *)
 exact 0.
Defined.

Lemma rel_shift1_twice_forwards_eq : forall W (Worder:preorder W) (ty:type 0)
  (A1 B1 A2 B2:Set) (R1 : W -> A1 -> B1 -> Prop) (R1kripke : kripke_relation Worder R1)
                    (R2 : W -> A2 -> B2 -> Prop) (R2kripke : kripke_relation Worder R2) w e1 e2 (x : ty_sem ty_nil ty),
  ty_rel (R1kripke;;R2kripke;;rel_nil Worder) (shift1 (shift1 ty)) w (coerce e1 x) (coerce e2 x).
intros. 
rewrite <- rel_shift1_twice_equal with (t1:=x) (t2:=x).
 change (rel_nil natorder) with (diagonal natorder ty_nil). rewrite rel_diagonal. reflexivity.
 symmetry. apply coerce_jmeq.
 symmetry. apply coerce_jmeq.
Save.

Lemma rel_shift1_twice_forwards_eq2 : forall W (Worder:preorder W) (ty:type 0)
  (A1 B1 A2 B2:Set) (R1 : W -> A1 -> B1 -> Prop) (R1kripke : kripke_relation Worder R1)
                    (R2 : W -> A2 -> B2 -> Prop) (R2kripke : kripke_relation Worder R2) w x y,
  JMeq x y ->
  ty_rel (R1kripke;;R2kripke;;rel_nil Worder) (shift1 (shift1 ty)) w x y.
intros. 
rewrite <- rel_shift1_twice_equal with (t1:=(coerce (ty_shift1_twice_equal ty ty_nil A1 A2) x)) (t2:=coerce (ty_shift1_twice_equal ty ty_nil B1 B2) y).
 change (rel_nil natorder) with (diagonal natorder ty_nil). rewrite rel_diagonal.
  apply JMeq_eq. eapply JMeq_trans. (*transitivity x.*)
   apply coerce_jmeq.
   eapply JMeq_trans. (*transitivity y.*)
    apply H.
    symmetry. apply coerce_jmeq.
 apply coerce_jmeq.
 apply coerce_jmeq.
Save.

Ltac by_transitivity Worder := repeat first [ eassumption | eapply (preorder_trans Worder) ].

Lemma to_state_term_wf : forall tA tS (t : ty_sem ty_nil (stmonad tA tS)), wf_pre_state_term 0 (to_pre_state_term t).
unfold ty_sem. unfold to_pre_state_term. simpl.
intros tA tS [t P].
set (R:=fun w x (y :unit)=> forall w', natorder w w' -> x w' < w').
assert (Rkripke:kripke_relation natorder R).
 unfold kripke_relation. unfold R. intros. apply H0. eapply (preorder_trans natorder); eassumption.

pose (P nat natorder
        (nat -> nat) unit
        (fun w x y => forall w', natorder w w' -> x w' < w')
         Rkripke).
generalize p. clear p.
intros. simpl.
destruct (t (nat -> nat)) as [t2 P2].
intros.
assert (R'kripke:kripke_relation natorder (fun w (x:nat -> pre_state_term (ty_sem ty_nil tA) (ty_sem ty_nil tS)) (y:unit) => forall w', natorder w w' -> wf_pre_state_term w' (x w'))).
 unfold kripke_relation. intros. apply H0. eapply (preorder_trans natorder); eassumption.

refine (p 0
          (nat -> pre_state_term (ty_sem ty_nil tA) (ty_sem ty_nil tS)) unit
          (fun w x y => forall w', natorder w w' -> wf_pre_state_term w' (x w'))
          R'kripke
          0
          _
          (fun _ => tt)
          _ _
          0
          _
          (fun _ _ => tt)
          _ _
          0
          _
          (fun _ _ => tt)
          _ _
          0
          _
          (fun _ _ _ => tt)
          _ _
          _ _).

(* 0 <= 0 *)
apply (preorder_refl natorder).

(* ret preserves the relation *)
intros. apply wf_stop.

(* 0 <= 0 *)
apply (preorder_refl natorder).

(* new preserves the relation *)
intros. apply wf_new.
apply H2 with (w':=S w'0).
 apply tt.
 unfold natorder. simpl. omega.
 unfold natorder. simpl. intros. unfold natorder in H3. simpl in H3. omega.
 unfold natorder. simpl. unfold natorder in H3. simpl in H3. omega.

(* 0 <= 0 *)
apply (preorder_refl natorder).

(* lookup preserves the relation *)
intros. apply wf_lookup.
apply H0. by_transitivity natorder.
intros. apply H2 with (w':=w'1) (x2:=(coerce (sym_eq (ty_shift1_twice_equal tS ty_nil unit unit)) i)).
 assumption.
 apply rel_shift1_twice_forwards_eq.
 apply (preorder_refl natorder).

(* 0 <= 0 *)
apply (preorder_refl natorder).

(* update preserves the relation *)
intros. apply wf_update.
 apply H0. by_transitivity natorder.
 apply H4. assumption.

(* 0 <= 0 *)
apply (preorder_refl natorder).
Save.

Definition to_state_term : forall tA tS,
  ty_sem ty_nil (stmonad tA tS) ->
  state_term (ty_sem ty_nil tA) (ty_sem ty_nil tS) 0.
intros tA tS t. 
apply wf_to_state_term with (t:=to_pre_state_term t).
apply to_state_term_wf.
Defined.

Definition from_state_term_inner : forall tA tS (A:Set),
  state_term (ty_sem ty_nil tA) (ty_sem ty_nil tS) 0 ->
  {x0 : forall A0 : Set,
       (projT1 (ty_sem_rel (shift1 (shift1 tA))) (A0;: A;: ty_nil) -> A0) ->
       (projT1 (ty_sem_rel (shift1 (shift1 tS))) (A0;: A;: ty_nil) ->
        (A -> A0) -> A0) ->
       (A ->
        (projT1 (ty_sem_rel (shift1 (shift1 tS))) (A0;: A;: ty_nil) -> A0) ->
        A0) ->
       (A ->
        projT1 (ty_sem_rel (shift1 (shift1 tS))) (A0;: A;: ty_nil) ->
        A0 -> A0) -> A0 |
     forall (W : Type) (Worder : preorder W) (A1 A2 : Set)
       (R : W -> A1 -> A2 -> Prop) (Rkripke : kripke_relation Worder R)
       (w w' : W)
       (x1 : projT1 (ty_sem_rel (shift1 (shift1 tA))) (A1;: A;: ty_nil) -> A1)
       (x2 : projT1 (ty_sem_rel (shift1 (shift1 tA))) (A2;: A;: ty_nil) -> A2),
     Worder w w' ->
     (forall (w'0 : W)
        (x3 : projT1 (ty_sem_rel (shift1 (shift1 tA))) (A1;: A;: ty_nil))
        (x4 : projT1 (ty_sem_rel (shift1 (shift1 tA))) (A2;: A;: ty_nil)),
      Worder w' w'0 ->
      projT2 (ty_sem_rel (shift1 (shift1 tA))) W Worder 
        (A1;: A;: ty_nil) (A2;: A;: ty_nil)
        (Rkripke;; @w_eq_kripke W Worder A;; rel_nil Worder) w'0 x3 x4 ->
      R w'0 (x1 x3) (x2 x4)) ->
     forall (w'0 : W)
       (x3 : projT1 (ty_sem_rel (shift1 (shift1 tS))) (A1;: A;: ty_nil) ->
             (A -> A1) -> A1)
       (x4 : projT1 (ty_sem_rel (shift1 (shift1 tS))) (A2;: A;: ty_nil) ->
             (A -> A2) -> A2),
     Worder w' w'0 ->
     (forall (w'1 : W)
        (x5 : projT1 (ty_sem_rel (shift1 (shift1 tS))) (A1;: A;: ty_nil))
        (x6 : projT1 (ty_sem_rel (shift1 (shift1 tS))) (A2;: A;: ty_nil)),
      Worder w'0 w'1 ->
      projT2 (ty_sem_rel (shift1 (shift1 tS))) W Worder 
        (A1;: A;: ty_nil) (A2;: A;: ty_nil)
        (Rkripke;; @w_eq_kripke W Worder A;; rel_nil Worder) w'1 x5 x6 ->
      forall (w'2 : W) (x7 : A -> A1) (x8 : A -> A2),
      Worder w'1 w'2 ->
      (forall (w'3 : W) (x9 x10 : A),
       Worder w'2 w'3 -> w_eq w'3 x9 x10 -> R w'3 (x7 x9) (x8 x10)) ->
      R w'2 (x3 x5 x7) (x4 x6 x8)) ->
     forall (w'1 : W)
       (x5 : A ->
             (projT1 (ty_sem_rel (shift1 (shift1 tS))) (A1;: A;: ty_nil) ->
              A1) -> A1)
       (x6 : A ->
             (projT1 (ty_sem_rel (shift1 (shift1 tS))) (A2;: A;: ty_nil) ->
              A2) -> A2),
     Worder w'0 w'1 ->
     (forall (w'2 : W) (x7 x8 : A),
      Worder w'1 w'2 ->
      w_eq w'2 x7 x8 ->
      forall (w'3 : W)
        (x9 : projT1 (ty_sem_rel (shift1 (shift1 tS))) (A1;: A;: ty_nil) ->
              A1)
        (x10 : projT1 (ty_sem_rel (shift1 (shift1 tS))) (A2;: A;: ty_nil) ->
               A2),
      Worder w'2 w'3 ->
      (forall (w'4 : W)
         (x11 : projT1 (ty_sem_rel (shift1 (shift1 tS))) (A1;: A;: ty_nil))
         (x12 : projT1 (ty_sem_rel (shift1 (shift1 tS))) (A2;: A;: ty_nil)),
       Worder w'3 w'4 ->
       projT2 (ty_sem_rel (shift1 (shift1 tS))) W Worder 
         (A1;: A;: ty_nil) (A2;: A;: ty_nil)
         (Rkripke;; @w_eq_kripke W Worder A;; rel_nil Worder) w'4 x11 x12 ->
       R w'4 (x9 x11) (x10 x12)) -> R w'3 (x5 x7 x9) (x6 x8 x10)) ->
     forall (w'2 : W)
       (x7 : A ->
             projT1 (ty_sem_rel (shift1 (shift1 tS))) (A1;: A;: ty_nil) ->
             A1 -> A1)
       (x8 : A ->
             projT1 (ty_sem_rel (shift1 (shift1 tS))) (A2;: A;: ty_nil) ->
             A2 -> A2),
     Worder w'1 w'2 ->
     (forall (w'3 : W) (x9 x10 : A),
      Worder w'2 w'3 ->
      w_eq w'3 x9 x10 ->
      forall (w'4 : W)
        (x11 : projT1 (ty_sem_rel (shift1 (shift1 tS))) (A1;: A;: ty_nil))
        (x12 : projT1 (ty_sem_rel (shift1 (shift1 tS))) (A2;: A;: ty_nil)),
      Worder w'3 w'4 ->
      projT2 (ty_sem_rel (shift1 (shift1 tS))) W Worder 
        (A1;: A;: ty_nil) (A2;: A;: ty_nil)
        (Rkripke;; @w_eq_kripke W Worder A;; rel_nil Worder) w'4 x11 x12 ->
      forall (w'5 : W) (x13 : A1) (x14 : A2),
      Worder w'4 w'5 ->
      R w'5 x13 x14 -> R w'5 (x7 x9 x11 x13) (x8 x10 x12 x14)) ->
     R w'2 (x0 A1 x1 x3 x5 x7) (x0 A2 x2 x4 x6 x8)}.
intros tA tS V t.
exists (fun (M:Set) ret new lkup upd =>
          let coercionA:=(sym_eq (ty_shift1_twice_equal tA ty_nil M V)) in
          let coercionS:=(sym_eq (ty_shift1_twice_equal tS ty_nil M V)) in
          state_term_rec (fun n _ => vec V n -> M)
            (fun n a       env => ret (coerce coercionA a))
            (fun n s _ f   env => new (coerce coercionS s) (fun x => f (vec_cons x env)))
            (fun n v l _ f env => lkup (idx l env) (fun s => f (coerce (sym_eq coercionS) s) env))
            (fun n v l s _ f env => upd (idx l env) (coerce coercionS s) (f env))
            t (vec_nil V)).
simpl. intros.

set (w2:=w'2).
assert (orderH:Worder w'2 w2). apply (preorder_refl Worder).
assert (envH:forall i (l:i<0) w, Worder w2 w -> (idx l (vec_nil V)) = (idx l (vec_nil V))).
 intros. inversion l.
generalize w2 orderH envH. clear w2 orderH envH.
generalize (vec_nil V) at 1 3.
generalize (vec_nil V) at 1 2.
generalize t. clear t. 
generalize 0 at 3 4 5 6 7 8 87 166.

induction t; intros.
 (* Stop *)
 simpl. apply H0.
  by_transitivity Worder.
  apply rel_shift1_twice_forwards_eq.
 (* New *)
 simpl. apply H2 with (w'1:=w2). 
  by_transitivity Worder.
  apply rel_shift1_twice_forwards_eq.
  apply (preorder_refl Worder).
  intros. apply IHt.
   by_transitivity Worder.
   intros. destruct i. 
    simpl. apply H8.
    simpl. apply envH with (w:=w2).
     apply (preorder_refl Worder).
 (* Lookup *)
 simpl. apply H4 with (w'2:=w2).
  by_transitivity Worder.
  unfold w_eq. apply envH with (w:=w2). apply (preorder_refl Worder).
  apply (preorder_refl Worder).
  intros.
  assert (ty_rel (rel_nil Worder) tS w'4 (coerce (sym_eq (sym_eq (ty_shift1_twice_equal tS ty_nil A1 V))) x11)
                                         (coerce (sym_eq (sym_eq (ty_shift1_twice_equal tS ty_nil A2 V))) x12)).
   rewrite rel_shift1_twice_equal with (t1':=x11) (t2':=x12) (RAkripke:=Rkripke) (RBkripke:=@w_eq_kripke W Worder V).
   apply H9.
   apply coerce_jmeq.
   apply coerce_jmeq.
  change (rel_nil Worder) with (diagonal Worder ty_nil) in H10.
  rewrite rel_diagonal in H10.
  rewrite H10.
  apply H7.
   by_transitivity Worder.
   intros. apply envH with (w:=w2). apply (preorder_refl Worder).
 (* Update *)
 simpl. apply H6 with (w'3:=w2) (w'4:=w2).
  assumption.
  unfold w_eq. apply envH with (w:=w2). apply (preorder_refl Worder).
  apply (preorder_refl Worder).
  apply rel_shift1_twice_forwards_eq.
  apply (preorder_refl Worder).
  apply IHt.
   assumption.
   assumption.
Defined.

Definition from_state_term : forall tA tS,
  state_term (ty_sem ty_nil tA) (ty_sem ty_nil tS) 0 -> ty_sem ty_nil (stmonad tA tS).
unfold ty_sem at 3.
intros tA tS x.
unfold stmonad.
simpl.
exists (fun A => from_state_term_inner tA tS A x).
(* now we have to prove parametricity all over again, except in a larger context with another relation *)
unfold from_state_term_inner. simpl. intros.

set (w2:=w'2).
assert (orderH:Worder w'2 w2). apply (preorder_refl Worder).
assert (envH:forall i (l:i<0) w, Worder w2 w -> R w (idx l (vec_nil A1)) (idx l (vec_nil A2))).
 intros. inversion l.
generalize w2 orderH envH. clear w2 orderH envH.
generalize (vec_nil A1).
generalize (vec_nil A2).
generalize x. clear x.
generalize 0 at 3 4 5 6 7 8 87 166.

induction x; intros.
 (* Stop *)
 simpl. apply H0.
  by_transitivity Worder.
  apply rel_shift1_twice_forwards_eq.
 (* New *)
 simpl. apply H2 with (w':=w2).
  by_transitivity Worder.
  apply rel_shift1_twice_forwards_eq.
  apply (preorder_refl Worder).
  intros. apply IHx.
   by_transitivity Worder.
   intros. destruct i.
    simpl. apply (Rkripke w'3 w0 x8 x9 H9 H8). 
    simpl. apply envH.
     by_transitivity Worder.
 (* Lookup *)
 simpl. apply H4 with (w':=w2).
  by_transitivity Worder.
  apply envH. apply (preorder_refl Worder).
  apply (preorder_refl Worder).
  intros.
  assert (ty_rel (rel_nil Worder) tS w'3 (coerce (sym_eq (sym_eq (ty_shift1_twice_equal tS ty_nil A0 A1))) x8)
                                         (coerce (sym_eq (sym_eq (ty_shift1_twice_equal tS ty_nil A3 A2))) x9)).
   rewrite rel_shift1_twice_equal with (t1':=x8) (t2':=x9) (RAkripke:=Rkripke0) (RBkripke:=Rkripke).
    apply H9.
    apply coerce_jmeq.
    apply coerce_jmeq.
  change (rel_nil Worder) with (diagonal Worder ty_nil) in H10.
  rewrite rel_diagonal in H10.
  rewrite H10.
  apply H7.
   by_transitivity Worder.
   intros. apply envH. by_transitivity Worder.
 (* Update *)
 simpl. apply H6 with (w':=w2) (w'0:=w2).
  assumption.
  apply envH. apply (preorder_refl Worder).
  apply (preorder_refl Worder).
  apply rel_shift1_twice_forwards_eq.
  apply (preorder_refl Worder).
  apply IHx.
   assumption.
   assumption.
Defined.

Lemma coerce_twice_jmeq : forall (A B C:Set) (eqp:A = B) (eqp':B=C) x,
  JMeq (coerce eqp (coerce eqp' x)) x.
intros. eapply JMeq_trans; apply coerce_jmeq.
Save.

Lemma state_iso1aux : forall tA tS (t : pre_state_term (ty_sem ty_nil tA) (ty_sem ty_nil tS)) (wf:wf_pre_state_term 0 t),
  to_pre_state_term (from_state_term tA tS (wf_to_state_term wf)) = t.
unfold to_pre_state_term. unfold from_state_term. unfold from_state_term_inner.

simpl.

intros tA tS t.

assert (forall i (l:i < 0) n', 0 <= n' -> idx l (vec_nil (nat -> nat)) n' = i + (n' - 0)).
 intros. inversion l.
generalize H. clear H.
generalize (vec_nil (nat -> nat)).
generalize 0 at 1 2 3 4 5 8 204 207 208.

induction t; intros.
 (* Stop *)
 simpl. apply f_equal.
  apply JMeq_eq. apply coerce_twice_jmeq.
 (* New *)
 simpl. apply f_equal2.
  apply JMeq_eq. apply coerce_twice_jmeq.
  apply IHt. intros. destruct i.
   simpl. reflexivity.
   simpl. replace (S (i + (n' - S n))) with (i + (n' - n)) by omega.
   apply H. omega.
 (* Lookup *)
 simpl. apply f_equal2.
  rewrite H0. omega. omega.
  ext d. 
   match goal with [ |- context [wf_to_state_term ?X] ] => generalize X end.
   assert ((@coerce
                 (@ty_sem 2
                    ((nat ->
                      pre_state_term (@ty_sem 0 ty_nil tA)
                        (@ty_sem 0 ty_nil tS));: (nat -> nat);: ty_nil)
                    (@shift1 1 (@shift1 0 tS))) (@ty_sem 0 ty_nil tS)
                 (@sym_eq Set
                    (@ty_sem 2
                       ((nat ->
                         pre_state_term (@ty_sem 0 ty_nil tA)
                           (@ty_sem 0 ty_nil tS));: 
                        (nat -> nat);: ty_nil) (@shift1 1 (@shift1 0 tS)))
                    (@ty_sem 0 ty_nil tS)
                    (@sym_eq Set (@ty_sem 0 ty_nil tS)
                       (@ty_sem 2
                          ((nat ->
                            pre_state_term (@ty_sem 0 ty_nil tA)
                              (@ty_sem 0 ty_nil tS));: 
                           (nat -> nat);: ty_nil) (@shift1 1 (@shift1 0 tS)))
                       (@ty_shift1_twice_equal 0 tS ty_nil
                          (nat ->
                           pre_state_term (@ty_sem 0 ty_nil tA)
                             (@ty_sem 0 ty_nil tS)) 
                          (nat -> nat))))
                 (@coerce (@ty_sem 0 ty_nil tS)
                    (@projT1 (ty_environment 2 -> Set)
                       (fun ty_sem : ty_environment 2 -> Set =>
                        forall (W : Type) (Worder : preorder W)
                          (e1 e2 : ty_environment 2),
                        @rel_environment W Worder 2 e1 e2 ->
                        W -> ty_sem e1 -> ty_sem e2 -> Prop)
                       (@ty_sem_rel 2 (@shift1 1 (@shift1 0 tS)))
                       ((nat ->
                         pre_state_term (@ty_sem 0 ty_nil tA)
                           (@ty_sem 0 ty_nil tS));: 
                        (nat -> nat);: ty_nil))
                    (@sym_eq Set (@ty_sem 0 ty_nil tS)
                       (@projT1 (ty_environment 2 -> Set)
                          (fun ty_sem : ty_environment 2 -> Set =>
                           forall (W : Type) (Worder : preorder W)
                             (e1 e2 : ty_environment 2),
                           @rel_environment W Worder 2 e1 e2 ->
                           W -> ty_sem e1 -> ty_sem e2 -> Prop)
                          (@ty_sem_rel 2 (@shift1 1 (@shift1 0 tS)))
                          ((nat ->
                            pre_state_term (@ty_sem 0 ty_nil tA)
                              (@ty_sem 0 ty_nil tS));: 
                           (nat -> nat);: ty_nil))
                       (@ty_shift1_twice_equal 0 tS ty_nil
                          (nat ->
                           pre_state_term (@ty_sem 0 ty_nil tA)
                             (@ty_sem 0 ty_nil tS)) 
                          (nat -> nat))) d)) = d).
    apply JMeq_eq. apply coerce_twice_jmeq.
   intro X. rewrite <- H1 at 2.
   apply H. apply H0.
 (* Update *)
 simpl. apply f_equal3.
  rewrite H. omega. omega.
  apply JMeq_eq. apply coerce_twice_jmeq.
  apply IHt.
  apply H.
Save.

Lemma hoas_iso1 : forall tA tS (t:state_term (ty_sem ty_nil tA) (ty_sem ty_nil tS) 0),
  to_state_term (from_state_term tA tS t) = t.
intros. unfold to_state_term.
replace t with (wf_to_state_term (proj2_sig (state_term_to_wf t))) by apply state_term_wf_iso1.
match goal with [ |- @wf_to_state_term _ _ _ _ ?X = _ ] => generalize X end. intro p. 
match goal with [ |- @wf_to_state_term _ _ (to_pre_state_term (from_state_term _ _ (wf_to_state_term ?X))) _ _ = _ ] => set (p1:=X) in * end. 

assert (to_pre_state_term (from_state_term _ _ (@wf_to_state_term _ _ (proj1_sig (state_term_to_wf t)) 0 p1))=proj1_sig (state_term_to_wf t))
    by apply state_iso1aux.
revert p. rewrite H. intro p.

replace p with p1 by apply proof_irrelevance.
reflexivity.
Save.

Lemma shift_twice_eq : forall W (Worder:preorder W) (A1 B1 A2 B2:Set) ty
  (R1 : W -> A1 -> B1 -> Prop) (R1kripke:kripke_relation Worder R1)
  (R2 : W -> A2 -> B2 -> Prop) (R2kripke:kripke_relation Worder R2) w x y,
  ty_rel (R2kripke;;R1kripke;;rel_nil Worder) (shift1 (shift1 ty)) w x y -> JMeq x y.
intros.
rewrite <- rel_shift1_twice_equal with (t1:=(coerce (ty_shift1_twice_equal ty ty_nil A2 A1) x))
                                       (t2:=(coerce (ty_shift1_twice_equal ty ty_nil B2 B1) y)) in H.
change (rel_nil Worder) with (diagonal Worder ty_nil) in H.
rewrite rel_diagonal in H.
apply JMeq_trans with (y:=coerce (ty_shift1_twice_equal ty ty_nil A2 A1) x).
 symmetry. apply coerce_jmeq.
 apply JMeq_trans with (y:=coerce (ty_shift1_twice_equal ty ty_nil B2 B1) y).
  rewrite H. reflexivity.
  apply coerce_jmeq.
apply coerce_jmeq.
apply coerce_jmeq.
Save.

Lemma state_iso2 : forall tA tS (t : ty_sem ty_nil (stmonad tA tS)),
  from_state_term tA tS (to_state_term t) = t.
unfold ty_sem. unfold from_state_term. unfold to_state_term. intros.
match goal with [ |- ?x = ?y ] => refine (sig_eq x y _) end. simpl in *. destruct t as [t P]. simpl in *.
ext V. unfold from_state_term_inner.
match goal with [ |- ?x = ?y ] => refine (sig_eq x y _) end.
simpl.
ext M. ext ret. ext new. ext lkup. ext upd.
match goal with [ |- context [wf_to_state_term ?X] ] => generalize X end. intro wf.
unfold to_pre_state_term in wf. simpl in wf.
change (vec_nil V) with (list_to_vec (@nil V)).
change 0 with (length (@nil V)).

match goal with [|- state_term_rec ?X1 ?X2 ?X3 ?X4 ?X5 _ _ = _ ] =>
  set (x1:=X1); set (x2:=X2); set (x3:=X3); set (x4:=X4); set (x5:=X5) end.

set (R1:=fun env x y => forall env', listorder V env env' -> nth_error env' (x (length env')) = Some y).
assert (R1kripke:kripke_relation (listorder V) R1).
 unfold kripke_relation. unfold R1. intros. apply H0. by_transitivity (listorder V).

set (R2:=fun env x y =>
            forall env', listorder V env env' ->
              forall p0, state_term_rec x1 x2 x3 x4 x5 (@wf_to_state_term _ _ (x (length env')) (length env') p0) (list_to_vec env') = y).
assert (R2kripke:kripke_relation (listorder V) R2).
 unfold kripke_relation. unfold R2. intros. apply H0. by_transitivity (listorder V).

refine (P (list V) (listorder V)
          (nat -> nat) V
          R1 R1kripke
          (@nil V)
          (nat -> pre_state_term (ty_sem ty_nil tA) (ty_sem ty_nil tS)) M
          R2 R2kripke
          (@nil V) _ ret _ _ (* ret *)
          (@nil V) _ new _ _ (* new *)
          (@nil V) _ lkup _ _ (* lookup *)
          (@nil V) _ upd _ _ (* update *)
          (@nil V) _ wf).

(* [] <= [] *)
apply (preorder_refl (listorder V)).

(* ret is related *)
unfold R2. intros. simpl. unfold x2. apply f_equal.
 apply JMeq_eq. eapply JMeq_trans. (*transitivity x0. *)
  apply coerce_twice_jmeq.
  eapply shift_twice_eq. apply H0.

(* [] <= [] *)
apply (preorder_refl (listorder V)).

(* new is related *)
unfold R2. unfold x3. intros. simpl. apply f_equal2.
 apply JMeq_eq. eapply JMeq_trans. (*transitivity x0.*)
  apply coerce_twice_jmeq.
  eapply shift_twice_eq. apply H0.
 ext loc. eapply H2 with (w':=loc::env') (env':=loc::env').
  unfold listorder. simpl. destruct H3. exists (loc::x). simpl. rewrite <- H3. reflexivity.
  unfold R1. intros. destruct H4. subst env'0. apply lookup_prop.
  apply (preorder_refl (listorder V)).

(* [] <= [] *)
apply (preorder_refl (listorder V)).

(* lookup is related *)
unfold R1. unfold R2. unfold x4. simpl. intros. apply f_equal2.
 apply lookup_idx. apply H0. destruct H1. destruct H3. rewrite H3. rewrite H1. exists (x9 ++ x). symmetry. apply app_ass.
 ext s. apply H2 with (w':=env').
  assumption.
  apply rel_shift1_twice_forwards_eq2. apply coerce_twice_jmeq.
  exists (@nil V). reflexivity.

(* [] <= [] *)
apply (preorder_refl (listorder V)).

(* update is related *)
unfold R1. unfold R2. unfold x5. simpl. intros. apply f_equal3.
 apply lookup_idx. apply H0. destruct H1. destruct H3. destruct H5. rewrite H5. rewrite H3. rewrite H1. exists (x12 ++ x11 ++ x). symmetry. rewrite app_ass. rewrite app_ass. reflexivity.
 apply JMeq_eq. eapply JMeq_trans. (*transitivity x7.*)
  apply coerce_twice_jmeq.
  eapply shift_twice_eq. apply H2.
  apply H4. assumption.

(* [] <= [] *)
apply (preorder_refl (listorder V)).
Save.


