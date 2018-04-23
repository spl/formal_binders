(***************************************************************************
* Church-Rosser Property in Pure Lambda-Calculus - Proofs                  *
* Arthur Charguéraud, March 2007, Coq v8.1                                 *
***************************************************************************)

Set Implicit Arguments.
Require Import Metatheory Lambda_Definitions Lambda_Infrastructure.


(* ********************************************************************** *)
(** ** Main Development *)

(* ********************************************************************** *)
(** Putting constructors as hints for auto *)

Hint Constructors beta star_ equiv_ iter_.

Hint Resolve para_var para_app.

Hint Extern 1 (para (trm_abs _) (trm_abs _)) =>
  let y := fresh "y" in apply_fresh para_abs as y.

Hint Extern 1 (para (trm_app (trm_abs _) _) (_ ^^ _)) =>
  let y := fresh "y" in apply_fresh para_red as y.

(* ********************************************************************** *)
(** Some relations between the properties of relations *)

Lemma red_all_to_out : forall (R : relation),
  red_all R -> red_refl R -> red_out R.
Proof.
  introz. auto*.
Qed.

Lemma red_out_to_rename : forall (R : relation),
  red_out R -> red_rename R.
Proof.
  introz.
  rewrite* (@subst_intro x t).
  rewrite* (@subst_intro x t').
Qed.

Lemma red_all_to_through : forall (R : relation),
  red_regular R -> red_all R -> red_through R.
Proof.
  introz. puts (H _ _ H4).
  rewrite* (@subst_intro x t1).
  rewrite* (@subst_intro x u1).
Qed.

(* ********************************************************************** *)
(** Properties of beta relation *)

Lemma beta_red_out : red_out beta.
Proof.
  introz. induction H0; simpl.
  rewrite* subst_open.
  apply* beta_app1.
  apply* beta_app2.
  apply_fresh* beta_abs as y. cross*.
Qed.

Lemma beta_red_rename : red_rename beta.
Proof.
  apply* (red_out_to_rename beta_red_out).
Qed.

(* ********************************************************************** *)
(** Properties of beta star relation *)

Lemma beta_star_app1 : forall t1 t1' t2,
  (beta star) t1 t1' -> term t2 ->
  (beta star) (trm_app t1 t2) (trm_app t1' t2).
Proof.
  intros. induction H.
  apply* star_refl.
  apply* (@star_trans beta (trm_app t0 t2)).
  apply* star_step.
Qed.

Lemma beta_star_app2 : forall t1 t2 t2',
  (beta star) t2 t2' -> term t1 ->
  (beta star) (trm_app t1 t2) (trm_app t1 t2').
Proof.
  intros. induction H.
  apply* star_refl.
  apply* (@star_trans beta (trm_app t1 t2)).
  apply* star_step.
Qed.

Lemma beta_star_abs : forall L t1 t1',
  (forall x, x \notin L -> (beta star) (t1 ^ x) (t1' ^ x)) ->
  (beta star) (trm_abs t1) (trm_abs t1').
Proof.
  introv R. pick_fresh x. forward~ (R x) as Red.
  asserts B1 (term (trm_abs t1')).
    apply_fresh term_abs as y. forward* (R y).
  asserts B2 (term (trm_abs t1')).
    apply_fresh term_abs as y. forward* (R y).
  gen_eq (t1 ^ x) as u. gen_eq (t1' ^ x) as u'.
  clear R. gen t1 t1'.
  induction Red; intros; subst.
  rewrite* (@open_var_inj x t1 t1').
  destruct~ (@close_var_spec t2 x) as [u [P [Q R]]].
   apply* (@star_trans beta (trm_abs u)).
  apply star_step.
   apply_fresh* beta_abs as y.
   apply* (@beta_red_rename x).
Qed.

Lemma beta_star_red_in : red_in (beta star).
Proof.
  introv Wf Red. puts term. induction Wf; simpl.
  case_var*.
  apply~ (@star_trans beta (trm_app ([x ~> u']t1) ([x ~> u]t2))).
    apply* beta_star_app1.
    apply* beta_star_app2.
  apply_fresh* beta_star_abs as y. cross*.
Qed.

Lemma beta_star_red_all : red_all (beta star).
Proof.
  introv Redt. induction Redt; simpl; intros u u' Redu.
  apply* beta_star_red_in.
  apply* (@star_trans beta ([x ~> u]t2)).
  apply* (@star_trans beta ([x ~> u]t')).
   apply* star_step. apply* beta_red_out.
   apply* beta_star_red_in.
Qed.

Lemma beta_star_red_through : red_through (beta star).
Proof.
  apply (red_all_to_through red_regular_beta_star beta_star_red_all).
Qed.

(* ********************************************************************** *)
(** Properties of parallel relation and its iterated version *)

Section ParaProperties.

Hint Extern 1 (para (if _ == _ then _ else _) _) => case_var.

Lemma para_red_all : red_all para.
Proof.
  intros x t t' H. induction H; intros; simpl*.
  rewrite* subst_open. apply_fresh* para_red as y. cross*.
  apply_fresh* para_abs as y. cross*.
Qed.

Lemma para_red_refl : red_refl para.
Proof.
  introz. induction* H.
Qed.

Lemma para_red_out : red_out para.
Proof.
  apply* (red_all_to_out para_red_all para_red_refl).
Qed.

Lemma para_red_rename : red_rename para.
Proof.
  apply* (red_out_to_rename para_red_out).
Qed.

Lemma para_red_through : red_through para.
Proof.
  apply* (red_all_to_through red_regular_para para_red_all).
Qed.

Lemma para_iter_red_refl : red_refl (para iter).
Proof.
  introz. use para_red_refl.
Qed.

End ParaProperties.

(* ********************************************************************** *)
(** Confluence of parallel relation *)

Lemma para_abs_inv : forall t1 u,
  para (trm_abs t1) u -> exists L, exists t2, u = (trm_abs t2) /\
  forall x : var, x \notin L -> para (t1 ^ x) (t2 ^ x).
Proof.
  intros. inversion* H.
Qed.

Lemma para_confluence : confluence para.
Proof.
  introv HS. gen T. induction HS; intros T HT; inversions HT.
    (* case: red / red *)
  destructi~ (IHHS t2'0) as [u2 [U2a U2b]].
  pick_fresh x. forward~ (H0 x) as K.
  destruct~ (K (t1'0 ^ x)) as [u1x [U1a U1b]].
  destruct~ (@close_var_spec u1x x) as [u1 [EQu1 termu1]].
  rewrite EQu1 in U1a, U1b.
  exists (u1 ^^ u2). split; apply* (@para_red_through x).
    (* case: red / trm_app *)
  destructi~ (IHHS t2'0) as [u2 [U2a U2b]].
  destruct (para_abs_inv H3) as [L2 [t1'0x [EQ Ht1'0]]].
  rewrite EQ in H3 |- *.
  pick_fresh x. forward~ (H0 x) as K.
  destruct ~ (K (t1'0x ^ x)) as [u1x [U1a U1b]].
  destruct~ (@close_var_spec u1x x) as [u1 [EQu1 termu1]].
  rewrite EQu1 in U1a, U1b.
  exists (u1 ^^ u2). split.
    apply* (@para_red_through x).
    apply_fresh para_red as y; auto.
     apply* (@para_red_rename x).
    (* case: var / var *)
  auto*.
    (* case: trm_app / red *)
  destruct~ (IHHS2 t2'0) as [u2 [U2a U2b]].
  destruct (para_abs_inv HS1) as [L2 [t1'x [EQ Ht1'x]]].
  destruct (IHHS1 (trm_abs t1'0)) as [u1x [U1a U1b]].
   apply_fresh* para_abs as y.
  rewrite EQ in HS1, U1a |- *.
  destruct (para_abs_inv U1b) as [L1 [u1 [EQ' Hu1]]].
  rewrite EQ' in U1a, U1b.
  exists (u1 ^^ u2). split.
    inversion U1a. apply* (@para_red L0).
    pick_fresh x. apply* (@para_red_through x).
    (* case: trm_app / trm_app *)
  destructi~ (IHHS1 t1'0) as [P1 [HP11 HP12]].
  destructi~ (IHHS2 t2'0) as [P2 [HP21 HP22]].
  exists* (trm_app P1 P2).
    (* case: trm_abs / trm_abs *)
  pick_fresh x. forward~ (H0 x) as K.
  destruct~ (K (t1'0 ^ x)) as [px [P0 P1]].
  destruct~ (@close_var_spec px x) as [p [EQP termp]].
  rewrite EQP in P0, P1.
  exists (trm_abs p). split;
   apply_fresh* para_abs as y; apply* (@para_red_rename x).
Qed.

(* ********************************************************************** *)
(** Confluence of iterated parallel relation *)

Lemma para_iter_parallelogram :
  forall M S, (para iter) M S -> forall T, para M T ->
    exists P : trm, para S P /\ (para iter) T P.
Proof.
  introv H. induction H; introv MtoT.
  destructi~ (IHiter_1 T) as [P [HP1 HP2]].
   destructi~ (IHiter_2 P) as [Q [HQ1 HQ2]].
   exists Q. use (@iter_trans para P).
  destruct* (para_confluence H MtoT).
Qed.

Lemma para_iter_confluence : confluence (para iter).
Proof.
  introv MtoS MtoT. gen T.
  induction MtoS; introv MtoT.
  destructi~ (IHMtoS1 T) as [P [HP1 HP2]].
   destructi~ (IHMtoS2 P) as [Q [HQ1 HQ2]]. exists* Q.
  destruct* (para_iter_parallelogram MtoT H).
Qed.

(* ********************************************************************** *)
(** Equality of beta star and iterated parallel relations *)

Lemma beta_star_to_para_iter :
  (beta star) simulated_by (para iter).
Proof.
  introz. induction* H.
  apply* para_iter_red_refl.
  apply iter_step. induction H; use para_red_refl.
Qed.

Lemma para_iter_to_beta_star :
  (para iter) simulated_by (beta star).
Proof.
  introz. induction H; eauto.
  induction H.
  apply~ (@star_trans beta (t1 ^^ t2)).
   pick_fresh x. apply* (@beta_star_red_through x).
  apply* star_refl.
  apply~ (@star_trans beta (trm_app t1' t2)).
   apply* beta_star_app1. apply* beta_star_app2.
  apply* beta_star_abs.
Qed.

(* ********************************************************************** *)
(** Church-Rosser property of beta relation *)

Lemma beta_star_confluence : confluence (beta star).
Proof.
  introz. destruct (@para_iter_confluence M S T).
  use beta_star_to_para_iter.
  use beta_star_to_para_iter.
  use para_iter_to_beta_star.
Qed.

Lemma beta_church_rosser : church_rosser beta.
Proof.
  introz. induction H.
  exists* t.
  destruct* IHequiv_.
  destruct IHequiv_1 as [u [Pu Qu]].
   destruct IHequiv_2 as [v [Pv Qv]].
   destruct (beta_star_confluence Qu Pv) as [w [Pw Qw]].
   exists w. split.
     apply* (@star_trans beta u).
     apply* (@star_trans beta v).
  exists* t'.
Qed.
