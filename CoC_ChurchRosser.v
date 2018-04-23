(***************************************************************************
* Calculus of Constructions - Church-Rosser Property                       *
* Arthur Charguéraud, April 2007, Coq v8.1                                 *
***************************************************************************)

Set Implicit Arguments.
Require Import Metatheory CoC_Definitions CoC_Infrastructure CoC_BetaStar.


(* ********************************************************************** *)
(** ** Additional Definitions Used in this Proof *)

(* ********************************************************************** *)
(** Definition of parallel reduction *)

Inductive para : relation :=
  | para_red : forall L t1 t2 t2' u u',
      term t1 ->
      (forall x, x \notin L -> para (t2 ^ x) (t2' ^ x) ) ->
      para u u' ->
      para (trm_app (trm_abs t1 t2) u) (t2' ^^ u')
  | para_var : forall x,
      para (trm_fvar x) (trm_fvar x)
  | para_srt : forall n,
      para (trm_type n) (trm_type n)
  | para_app : forall t1 t1' t2 t2',
      para t1 t1' ->
      para t2 t2' ->
      para (trm_app t1 t2) (trm_app t1' t2')
  | para_abs : forall L t1 t1' t2 t2',
     para t1 t1' ->
     (forall x, x \notin L -> para (t2 ^ x) (t2' ^ x) ) ->
     para (trm_abs t1 t2) (trm_abs t1' t2')
  | para_prod : forall L t1 t1' t2 t2',
     para t1 t1' ->
     (forall x, x \notin L -> para (t2 ^ x) (t2' ^ x) ) ->
     para (trm_prod t1 t2) (trm_prod t1' t2').


(* ********************************************************************** *)
(** Definition of the transitive closure of a relation *)

Inductive iter_ (R : relation) : relation :=
  | iter_trans : forall t2 t1 t3,
      iter_ R t1 t2 -> iter_ R t2 t3 -> iter_ R t1 t3
  | iter_step : forall t t',
      R t t' -> iter_ R t t'.

Notation "R 'iter'" := (iter_ R) (at level 69).

(* ********************************************************************** *)
(** ** Lemmas Associated to Additional Definitions *)

Hint Constructors para iter_.

(* ********************************************************************** *)
(** Regularity *)

Lemma red_regular_para : red_regular para.
Proof.
  introz. induction* H.
Qed.

Lemma red_regular_para_iter : red_regular (para iter).
Proof.
  introz. induction* H. apply* red_regular_para.
Qed.

Hint Extern 1 (term ?t) => match goal with
  | H: para t _ |- _ => apply (proj1 (red_regular_para H))
  | H: para _ t |- _ => apply (proj2 (red_regular_para H))
  | H: (para iter) t _ |- _ => apply (proj1 (red_regular_para_iter))
  | H: (para iter) _ t |- _ => apply (proj2 (red_regular_para_iter))
  end.

(* ********************************************************************** *)
(** Automation *)

Hint Resolve para_var para_srt para_app.

Hint Extern 1 (para (trm_abs _ _) (trm_abs _ _)) =>
  let y := fresh "y" in apply_fresh para_abs as y.
Hint Extern 1 (para (trm_prod _ _) (trm_prod _ _)) =>
  let y := fresh "y" in apply_fresh para_prod as y.
Hint Extern 1 (para (trm_app (trm_abs _ _) _) (_ ^^ _)) =>
  let y := fresh "y" in apply_fresh para_red as y.


(* ********************************************************************** *)
(** Properties of parallel reduction and its iterated version *)

Section ParaProperties.

Hint Extern 1 (para (if _ == _ then _ else _) _) => case_var.

Lemma para_red_all : red_all para.
Proof.
  intros x t t' H. induction H; intros; simpl*.
  rewrite* subst_open. apply_fresh* para_red as y. cross*.
  apply_fresh* para_abs as y. cross*.
  apply_fresh* para_prod as y. cross*.
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
(** Equality of beta star and iterated parallel reductions *)

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
  apply~ (@star_trans beta (t2 ^^ u)).
   pick_fresh x. apply* (@beta_star_red_through x).
  apply* star_refl.
  apply* star_refl.
  apply~ (@star_trans beta (trm_app t1' t2)).
   apply* beta_star_app1. apply* beta_star_app2.
  apply~ (@star_trans beta (trm_abs t1' t2)).
    apply* beta_star_abs1. apply* beta_star_abs2.
  apply~ (@star_trans beta (trm_prod t1' t2)).
    apply* beta_star_prod1. apply* beta_star_prod2.
Qed.


(* ********************************************************************** *)
(** ** Proof of Church-Rosser Property for Beta Reduction *)

(* ********************************************************************** *)
(** Confluence of parallel reduction *)

Lemma para_abs_inv : forall t1 t2 u,
  para (trm_abs t1 t2) u -> exists L, exists t1' : trm, exists t2' : trm,
  u = (trm_abs t1' t2') /\ para t1 t1' /\
  forall x : var, x \notin L -> para (t2 ^ x) (t2' ^ x).
intros. inversion H. exists* L.
Qed.

Lemma para_prod_inv : forall t1 t2 u,
  para (trm_prod t1 t2) u -> exists L, exists t1' : trm, exists t2' : trm,
  u = (trm_prod t1' t2') /\ para t1 t1' /\
  forall x : var, x \notin L -> para (t2 ^ x) (t2' ^ x).
Proof.
  intros. inversion H. exists* L.
Qed.

Lemma para_confluence : confluence para.
Proof.
  introv HS. gen T. induction HS; intros T HT; inversions HT.
    (* case: red / red *)
  destructi~ (IHHS u'0) as [u2 [U2a U2b]].
  pick_fresh x. forward~ (H1 x) as K.
  destruct~ (K (t2'0 ^ x)) as [u1x [U1a U1b]].
  destruct~ (@close_var_spec u1x x) as [u1 [EQu1 termu1]].
  rewrite EQu1 in U1a, U1b.
  exists (u1 ^^ u2). split; apply* (@para_red_through x).
    (* case: red / trm_app *)
  destructi~ (IHHS t2'0) as [u2 [U2a U2b]].
  destruct (para_abs_inv H4) as [L2 [t1'0x [t2'0x [EQ [Ht1'0 Ht2'0]]]]].
  rewrite EQ in H4 |- *.
  pick_fresh x. forward~ (H1 x) as K.
  destruct~ (K (t2'0x ^ x)) as [u1x [U1a U1b]].
  destruct~ (@close_var_spec u1x x) as [u1 [EQu1 termu1]].
  rewrite EQu1 in U1a, U1b.
  exists (u1 ^^ u2). split.
    apply* (@para_red_through x).
    apply_fresh para_red as y; auto.
    apply* (@para_red_rename x).
    (* case: var / var *)
  auto*.
    (* case: srt / srt *)
  auto*.
    (* case: trm_app / red *)
  destruct~ (IHHS2 u') as [u2 [U2a U2b]].
  destruct (para_abs_inv HS1) as [L2 [t1'x [t2'x [EQ [Ht1'x Ht2'x]]]]].
  destruct (IHHS1 (trm_abs t1'x t2'0)) as [u1x [U1a U1b]]. auto.
  rewrite EQ in HS1, U1a |- *.
  destruct (para_abs_inv U1b) as [L1 [v1 [v2 [EQ' [Hv1 Hv2]]]]].
  rewrite EQ' in U1a, U1b.
  exists (v2 ^^ u2). split.
    inversion U1a. clear IHHS1 IHHS2 Hv2 U1a U1b.
    apply* (@para_red L0).
    pick_fresh x. apply* (@para_red_through x).
    (* case: trm_app / trm_app *)
  destructi~ (IHHS1 t1'0) as [P1 [HP11 HP12]].
  destructi~ (IHHS2 t2'0) as [P2 [HP21 HP22]].
  exists* (trm_app P1 P2).
    (* case: trm_abs / trm_abs *)
  pick_fresh x. forward~ (H0 x) as K.
  destruct~ (K (t2'0 ^ x)) as [px [P0 P1]].
  destructi~ (IHHS t1'0) as [u1 [HP1 HP2]].
  destruct~ (@close_var_spec px x) as [p [EQP termp]].
  rewrite EQP in P0, P1.
  exists (trm_abs u1 p). split;
   apply_fresh* para_abs as y; apply* (@para_red_rename x).
    (* case: trm_prod / trm_prod *)
  pick_fresh x. forward~ (H0 x) as K.
  destruct~ (K (t2'0 ^ x)) as [px [P0 P1]].
  destructi~ (IHHS t1'0) as [u1 [HP1 HP2]].
  destruct~ (@close_var_spec px x) as [p [EQP termp]].
  rewrite EQP in P0, P1.
  exists (trm_prod u1 p). split;
   apply_fresh* para_prod as y; apply* (@para_red_rename x).
Qed.

(* ********************************************************************** *)
(** Confluence of iterated parallel reduction *)

Lemma para_iter_parallelogram :
  forall M S, (para iter) M S -> forall T, para M T ->
  exists P : trm, para S P /\ (para iter) T P.
Proof.
  introv H. induction H; intros T MtoT.
  destructi~ (IHiter_1 T) as [P [HP1 HP2]].
   destructi~ (IHiter_2 P) as [Q [HQ1 HQ2]].
   exists Q. use (@iter_trans para P).
  destruct* (para_confluence H MtoT).
Qed.

Lemma para_iter_confluence : confluence (para iter).
Proof.
  introv MtoS MtoT. gen T.
  induction MtoS; intros T MtoT.
  destructi~ (IHMtoS1 T) as [P [HP1 HP2]].
   destructi~ (IHMtoS2 P) as [Q [HQ1 HQ2]]. exists* Q.
  destruct* (para_iter_parallelogram MtoT H).
Qed.

(* ********************************************************************** *)
(** Church-Rosser property of beta reduction *)

Lemma confluence_beta_star : confluence (beta star).
Proof.
  introz. destruct (@para_iter_confluence M S T).
  use beta_star_to_para_iter.
  use beta_star_to_para_iter.
  use para_iter_to_beta_star.
Qed.

Lemma church_rosser_beta : church_rosser beta.
Proof.
  introz. induction H.
  exists* t.
  destruct* IHequiv_.
  destruct IHequiv_1 as [u [Pu Qu]].
   destruct IHequiv_2 as [v [Pv Qv]].
   destruct (confluence_beta_star Qu Pv) as [w [Pw Qw]].
   exists w. split.
     apply* (@star_trans beta u).
     apply* (@star_trans beta v).
  exists* t'.
Qed.

