(***************************************************************************
* Safety for Simply Typed Lambda Calculus (CBV) - Proofs                   *
* Brian Aydemir & Arthur Charguéraud, July 2007, Coq v8.1                  *
***************************************************************************)

Set Implicit Arguments.
Require Import Metatheory
  STLC_Core_Definitions
  STLC_Core_Infrastructure.


(* ********************************************************************** *)
(** * Proofs *)

(** Typing is preserved by weakening. *)

Lemma typing_weaken : forall G E F t T,
   (E & G) |= t ~: T ->
   ok (E & F & G) ->
   (E & F & G) |= t ~: T.
Proof.
  introv Typ. gen_eq (E & G) as H. gen G.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  apply* typing_app.
Qed.

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall F U E t T z u,
  (E & z ~ U & F) |= t ~: T ->
  E |= u ~: U ->
  (E & F) |= [z ~> u]t ~: T.
Proof.
  introv Typt Typu. gen_eq (E & z ~ U & F) as G. gen F.
  induction Typt; introv Equ; subst; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs as y.
   rewrite* subst_open_var. apply_ih_bind* H0.
  apply* typing_app.
Qed.

(** Preservation (typing is preserved by reduction). *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t'.
  induction Typ; introv Red; inversions Red.
  inversions Typ1. pick_fresh x. rewrite* (@subst_intro x).
   apply_empty* typing_subst.
  apply* typing_app.
  apply* typing_app.
Qed.

(** Progress (a well-typed term is either a value or it can
  take a step of reduction). *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq (empty : env) as E. poses Typ' Typ.
  induction Typ; intros; subst.
  contradictions.
  left*.
  right. destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
      inversions Typ1; inversions Val1. exists* (t0 ^^ t2).
      exists* (trm_app t1 t2').
    exists* (trm_app t1' t2).
Qed.



