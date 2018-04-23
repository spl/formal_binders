(***************************************************************************
* Preservation and Progress for System-F with Subtyping - Proofs           *
* Brian Aydemir & Arthur Charguéraud, March 2007, Coq v8.1                 *
***************************************************************************)

Set Implicit Arguments.
Require Import Metatheory Fsub_Definitions Fsub_Infrastructure.

(** In parentheses are given the label of the corresponding
  lemma in the description of the POPLMark Challenge. *)


(* ********************************************************************** *)
(** * Properties of Subtyping *)

(* ********************************************************************** *)
(** Reflexivity (1) *)

Lemma sub_reflexivity : forall E T,
  okt E ->
  wft E T ->
  sub E T T .
Proof.
  introv Ok WI. poses W (type_from_wft WI). gen E.
  induction W; intros; inversions WI; eauto.
  apply_fresh* sub_all as Y.
Qed.

(* ********************************************************************** *)
(** Weakening (2) *)

Lemma sub_weakening : forall E F G S T,
   sub (E & G) S T ->
   okt (E & F & G) ->
   sub (E & F & G) S T.
Proof.
  introv Typ. gen_eq (E & G) as H. gen G.
  induction Typ; introv EQ Ok; subst; auto.
  (* case: fvar trans *)
  apply* sub_trans_tvar. apply* binds_weaken.
  (* case: all *)
  apply_fresh* sub_all as Y. apply_ih_bind* H0.
Qed.

(* ********************************************************************** *)
(** Narrowing and transitivity (3) *)

Section NarrowTrans.

Definition transitivity_on Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Hint Unfold transitivity_on.

Hint Resolve wft_narrow.

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub (E & Z ~<: Q & F) S T ->
  sub E P Q ->
  sub (E & Z ~<: P & F) S T.
Proof.
  introv TransQ SsubT PsubQ.
  gen_eq (E & Z ~<: Q & F) as G. gen F.
  induction SsubT; introv EQ; subst.
  apply* sub_top.
  apply* sub_refl_tvar.
  case (X == Z); intros EQ; subst.
    apply (@sub_trans_tvar P); puts (@okt_narrow Q).
      apply* binds_mid.
      apply TransQ.
        do_rew* concat_assoc (apply_empty* sub_weakening).
        binds_get H. auto*.
    apply* (@sub_trans_tvar U).
    binds_cases H; auto.
  apply* sub_arrow.
  apply_fresh* sub_all as Y. apply_ih_bind* H0.
Qed.

Lemma sub_transitivity : forall Q,
  transitivity_on Q.
Proof.
  intro Q. introv SsubQ QsubT. asserts* W (type Q).
  gen E S T. gen_eq Q as Q' eq. gen Q' eq.
  induction W; intros Q' EQ E S SsubQ;
    induction SsubQ; try discriminate; inversions EQ;
      intros T QsubT; inversions QsubT;
        eauto 4 using sub_trans_tvar.
  (* case: all / top -> only needed to fix well-formedness,
     by building back what has been deconstructed too much *)
  assert (sub E (typ_all S1 S2) (typ_all T1 T2)).
    apply_fresh* sub_all as y.
  auto*.
  (* case: all / all *)
  apply_fresh sub_all as Y. auto*.
  forward~ (H0 Y) as K. apply (K (T2 open_tt_var Y)); auto.
  puts (IHW T1). apply_empty* (@sub_narrowing_aux T1).
Qed.

Lemma sub_narrowing : forall Q E F Z P S T,
  sub E P Q ->
  sub (E & Z ~<: Q & F) S T ->
  sub (E & Z ~<: P & F) S T.
Proof.
  intros.
  apply* sub_narrowing_aux.
  apply* sub_transitivity.
Qed.

End NarrowTrans.

(* ********************************************************************** *)
(** Type substitution preserves subtyping (10) *)

Lemma sub_through_subst_tt : forall Q E F Z S T P,
  sub (E & Z ~<: Q & F) S T ->
  sub E P Q ->
  sub (E & map (subst_tb Z P) F) (subst_tt Z P S) (subst_tt Z P T).
Proof.
  introv SsubT PsubQ.
  gen_eq (E & Z ~<: Q & F) as G. gen F.
  induction SsubT; introv EQ; subst; simpl subst_tt.
  apply* sub_top.
  case_var.
    apply* sub_reflexivity.
    apply* sub_reflexivity.
     inversions H0. binds_cases H3. (* wf *)
      apply* (@wft_var U).
      apply* (@wft_var (subst_tt Z P U)). unsimpl_map_bind*.
   case_var.
    apply (@sub_transitivity Q).
      apply_empty* sub_weakening.
      rewrite* <- (@subst_tt_fresh Z P Q).
        binds_get H. auto*.
        apply* (@notin_fv_wf E). apply* fresh_mid.
    apply* (@sub_trans_tvar (subst_tt Z P U)).
      rewrite* (@map_subst_tb_id E Z P).
        binds_cases H; unsimpl_map_bind*.
        apply* fresh_mid.
  apply* sub_arrow.
  apply_fresh* sub_all as X.
   unsimpl (subst_tb Z P (bind_sub T1)).
   do 2 rewrite* subst_tt_open_tt_var.
   apply_ih_map_bind* H0.
Qed.

(* ********************************************************************** *)
(** * Properties of Typing *)

(* ********************************************************************** *)
(** Weakening (5) *)

Lemma typing_weakening : forall E F G e T,
   typing (E & G) e T ->
   okt (E & F & G) ->
   typing (E & F & G) e T.
Proof.
  introv Typ. gen_eq (E & G) as H. gen G.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as x. forward~ (H x) as K.
   apply_ih_bind (H0 x); eauto.
  apply* typing_app.
  apply_fresh* typing_tabs as X. forward~ (H X) as K.
   apply_ih_bind (H0 X); eauto.
  apply* typing_tapp. apply* sub_weakening.
  apply* typing_sub. apply* sub_weakening.
Qed.

(* ********************************************************************** *)
(** Strengthening (6) *)

Lemma sub_strengthening : forall x U E F S T,
  sub (E & x ~: U & F) S T ->
  sub (E & F) S T.
Proof.
  intros x U E F S T SsubT.
  gen_eq (E & x ~: U & F) as G. gen F.
  induction SsubT; introv EQ; subst; use wft_strengthen.
  (* case: fvar trans *)
  apply* (@sub_trans_tvar U0). binds_cases H; auto*.
  (* case: all *)
  apply_fresh* sub_all as X. apply_ih_bind* H0.
Qed.

(************************************************************************ *)
(** Preservation by Type Narrowing (7) *)

Lemma typing_narrowing : forall Q E F X P e T,
  sub E P Q ->
  typing (E & X ~<: Q & F) e T ->
  typing (E & X ~<: P & F) e T.
Proof.
  introv PsubQ Typ. gen_eq (E & X ~<: Q & F) as E'. gen F.
  induction Typ; introv EQ; subst.
  binds_cases H0; apply* typing_var.
  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  apply* typing_app.
  apply_fresh* typing_tabs as Y. apply_ih_bind* H0.
  apply* typing_tapp. apply* (@sub_narrowing Q).
  apply* typing_sub. apply* (@sub_narrowing Q).
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Lemma typing_through_subst_ee : forall U E F x T e u,
  typing (E & x ~: U & F) e T ->
  typing E u U ->
  typing (E & F) (subst_ee x u e) T.
Proof.
  introv TypT TypU. gen_eq (E & x ~: U & F) as E'. gen F.
  induction TypT; introv EQ; subst; simpl.
  case_var.
    binds_get H0. apply_empty* typing_weakening.
    binds_cases H0; apply* typing_var.
  apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih_bind* H0.
  apply* typing_app.
  apply_fresh* typing_tabs as Y.
    rewrite* subst_ee_open_te_var.
    apply_ih_bind* H0.
  apply* typing_tapp. apply* sub_strengthening.
  apply* typing_sub. apply* sub_strengthening.
Qed.

(************************************************************************ *)
(** Preservation by Type Substitution (11) *)

Lemma typing_through_subst_te : forall Q E F Z e T P,
  typing (E & Z ~<: Q & F) e T ->
  sub E P Q ->
  typing (E & map (subst_tb Z P) F) (subst_te Z P e) (subst_tt Z P T).
Proof.
  introv Typ PsubQ. gen_eq (E & Z ~<: Q & F) as G. gen F.
  induction Typ; introv EQ; subst; simpls subst_tt subst_te.
  apply* typing_var. rewrite* (@map_subst_tb_id E Z P).
   binds_cases H0; unsimpl_map_bind*. apply* fresh_mid.
  apply_fresh* typing_abs as y.
    unsimpl (subst_tb Z P (bind_typ V)).
    rewrite* subst_te_open_ee_var.
    apply_ih_map_bind* H0.
  apply* typing_app.
  apply_fresh* typing_tabs as Y.
    unsimpl (subst_tb Z P (bind_sub V)).
    rewrite* subst_te_open_te_var.
    rewrite* subst_tt_open_tt_var.
    apply_ih_map_bind* H0.
  rewrite* subst_tt_open_tt. apply* typing_tapp.
    apply* sub_through_subst_tt.
  apply* typing_sub. apply* sub_through_subst_tt.
Qed.

(* ********************************************************************** *)
(** * Preservation *)

(* ********************************************************************** *)
(** Inversions for Typing (13) *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (trm_abs S1 e1) T ->
  forall U1 U2, sub E T (typ_arrow U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x \notin L ->
     typing (E & x ~: S1) (e1 open_ee_var x) S2 /\ sub E S2 U2.
Proof.
  introv Typ. gen_eq (trm_abs S1 e1) as e. gen S1 e1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversions EQ.
  inversions* Sub. use (@sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall E S1 e1 T,
  typing E (trm_tabs S1 e1) T ->
  forall U1 U2, sub E T (typ_all U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X \notin L ->
     typing (E & X ~<: U1) (e1 open_te_var X) (S2 open_tt_var X)
     /\ sub (E & X ~<: U1) (S2 open_tt_var X) (U2 open_tt_var X).
Proof.
  intros E S1 e1 T H. gen_eq (trm_tabs S1 e1) as e. gen S1 e1.
  induction H; intros S1 b EQ U1 U2 Sub; inversion EQ.
  inversions Sub. splits. auto.
   exists T1. let L1 := gather_vars in exists L1.
   intros Y Fr. splits.
    apply_empty* (@typing_narrowing S1). auto.
  use (@sub_transitivity T).
Qed.

(* ********************************************************************** *)
(** Preservation Result (20) *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen e'. induction Typ; introv Red;
   try solve [ inversion Red ].
  (* case: app *)
  inversions Red; try solve [ apply* typing_app ].
  destructi (typing_inv_abs Typ1 (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply* sub_reflexivity.
    pick_fresh X. forward~ (P2 X) as K. destruct K.
     rewrite* (@subst_ee_intro X).
     apply_empty (@typing_through_subst_ee V).
       apply* (@typing_sub S2). apply_empty* sub_weakening.
       auto*.
  (* case: tapp *)
  inversions Red; try solve [ apply* typing_tapp ].
  destructi (typing_inv_tabs Typ (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply* sub_reflexivity.
    pick_fresh X. forward~ (P2 X) as K. destruct K.
     rewrite* (@subst_te_intro X).
     rewrite* (@subst_tt_intro X).
     unsimpl (E & map (subst_tb X T) empty).
     apply* (@typing_through_subst_te T1).
  (* case sub *)
  apply* typing_sub.
Qed.

(* ********************************************************************** *)
(** * Progress *)

(* ********************************************************************** *)
(** Canonical Forms (14) *)

Lemma canonical_form_abs : forall t U1 U2,
  value t -> typing empty t (typ_arrow U1 U2) ->
  exists V, exists e1, t = trm_abs V e1.
Proof.
  introv Val Typ. gen_eq (@empty bind) as E.
  gen_eq (typ_arrow U1 U2) as T. gen U1 U2.
  induction Typ; introv EQT EQE;
   try solve [ inversion Val | inversion EQT | eauto ].
    subst. inversion H. inversion H0. auto*.
Qed.

Lemma canonical_form_tabs : forall t U1 U2,
  value t -> typing empty t (typ_all U1 U2) ->
  exists V, exists e1, t = trm_tabs V e1.
Proof.
  introv Val Typ. gen_eq (@empty bind) as E.
  gen_eq (typ_all U1 U2) as T. gen U1 U2.
  induction Typ; introv EQT EQE;
   try solve [ inversion Val | inversion EQT | eauto ].
    subst. inversion H. inversion H0. auto*.
Qed.

(* ********************************************************************** *)
(** Progress Result (16) *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq (@empty bind) as E. poses Typ' Typ.
  induction Typ; intros EQ; subst.
  (* case: var *)
  inversion H0.
  (* case: abs *)
  left*.
  (* case: app *)
  right. destruct* IHTyp1 as [Val1 | [e1' Rede1']].
    destruct* IHTyp2 as [Val2 | [e2' Rede2']].
      destruct (canonical_form_abs Val1 Typ1) as [S [e3 EQ]].
        subst. exists* (open_ee e3 e2).
  (* case: tabs *)
  left*.
  (* case: tapp *)
  right. destruct* IHTyp as [Val1 | [e1' Rede1']].
    destruct (canonical_form_tabs Val1 Typ) as [S [e3 EQ]].
      subst. exists* (open_te e3 T).
      exists* (trm_tapp e1' T).
  (* case: sub *)
  auto*.
Qed.

