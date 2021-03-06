(***************************************************************************
* Safety for STLC with References - Infrastructure                         *
* Extented from "Type Safety for STLC"                                     *
* Arthur Charguéraud, July 2007, Coq v8.1                                  *
***************************************************************************)

Set Implicit Arguments.
Require Import Metatheory STLC_Ref_Definitions.

(* ********************************************************************** *)
(** ** Additional Definitions used in the Proofs *)

(** Computing free variables of a term. *)

Fixpoint fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i    => {}
  | trm_fvar x    => {{x}}
  | trm_abs t1    => (fv t1)
  | trm_app t1 t2 => (fv t1) \u (fv t2)
  | trm_unit      => {}
  | trm_loc l     => {}
  | trm_ref t1    => (fv t1)
  | trm_get t1    => (fv t1)
  | trm_set t1 t2 => (fv t1) \u (fv t2)
  end.

(** Substitution for names *)

Fixpoint subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => if x == z then u else (trm_fvar x)
  | trm_abs t1    => trm_abs (subst z u t1)
  | trm_app t1 t2 => trm_app (subst z u t1) (subst z u t2)
  | trm_unit      => trm_unit
  | trm_loc l     => trm_loc l
  | trm_ref t1    => trm_ref (subst z u t1)
  | trm_get t1    => trm_get (subst z u t1)
  | trm_set t1 t2 => trm_set (subst z u t1) (subst z u t2)
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).

(** Definition of the body of an abstraction *)

Definition body t :=
  exists L, forall x, x \notin L -> term (t ^ x).


(* ********************************************************************** *)
(** ** Instanciation of Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => {{ x }}) in
  let C := gather_vars_with (fun x : env => dom x) in
  let D := gather_vars_with (fun x : trm => fv x) in
  constr:(A \u B \u C \u D).

Ltac pick_fresh Y :=
  let L := gather_vars in (pick_fresh_gen L Y).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto*.

Hint Constructors term sto_ok value red.


(* ********************************************************************** *)
(** ** Properties of substitution *)

(* begin hide *)

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_rec_term_core :forall t j v i u, i <> j ->
  {j ~> v}t = {i ~> u}({j ~> v}t) -> t = {i ~> u}t.
Proof.
  induction t; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma open_rec_term : forall t u,
  term t -> forall k, t = {k ~> u}t.
Proof.
  induction 1; intros; simpl; f_equal*. unfolds open.
  pick_fresh x. apply* (@open_rec_term_core t1 0 (trm_fvar x)).
Qed.

(* end hide *)

(** Substitution for a fresh name is identity. *)

Lemma subst_fresh : forall x t u,
  x \notin fv t ->  [x ~> u] t = t.
Proof.
  intros. induction t; simpls; f_equal*.
  case_var*. notin_contradiction.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_open : forall x u t1 t2, term u ->
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. unfold open. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* open_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_var : forall x y u t, y <> x -> term u ->
  ([x ~> u]t) ^ y = [x ~> u] (t ^ y).
Proof.
  introv Neq Wu. rewrite* subst_open.
  simpl. case_var*.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_intro : forall x t u,
  x \notin (fv t) -> term u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv Fr Wu. rewrite* subst_open.
  rewrite* subst_fresh. simpl. case_var*.
Qed.


(* ********************************************************************** *)
(** ** Terms are stable through substitutions *)

(** Terms are stable by substitution *)

Lemma subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simpl*.
  case_var*.
  apply_fresh term_abs as y. rewrite* subst_open_var.
Qed.

Hint Resolve subst_term.


(* ********************************************************************** *)
(** ** Terms are stable through open *)

(** Conversion from locally closed abstractions and bodies *)

Lemma term_abs_to_body : forall t1,
  term (trm_abs t1) -> body t1.
Proof.
  intros. unfold body. inversion* H.
Qed.

Lemma body_to_term_abs : forall t1,
  body t1 -> term (trm_abs t1).
Proof.
  intros. inversion* H.
Qed.

Hint Resolve term_abs_to_body body_to_term_abs.

(** ** Opening a body with a term gives a term *)

Lemma open_term : forall t u,
  body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y. rewrite* (@subst_intro y).
Qed.

Hint Resolve open_term.


(* ********************************************************************** *)
(** ** Well-formedness of store *)

Lemma sto_ok_binds : forall mu l t,
   sto_ok mu -> binds l t mu -> term t.
Proof.
  unfolds binds. introv. induction mu as [|(l1,t1)];
   simpl; env_fix; introv Ok Binds.
  contradictions.
  inversions Ok. case_var.
    inversions* Binds.
    auto.
Qed.

Hint Resolve sto_ok_binds.


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** A typing relation holds only if the environment has no
   duplicated keys and the pre-term is locally-closed. *)

Lemma typing_regular : forall E P e T,
  typing E P e T -> ok E /\ term e.
Proof.
  split; induction H; auto*.
  pick_fresh y; forward~ (H0 y) as K. inversions* K.
Qed.

(** The value predicate only holds on locally-closed terms. *)

Lemma value_regular : forall e,
  value e -> term e.
Proof.
  induction 1; auto*.
Qed.

(** A reduction relation only holds only on well-formed objects. *)

Lemma red_regular : forall c c',
  red c c' ->
     (term (fst c) /\ term (fst c'))
  /\ (sto_ok (snd c) /\ sto_ok (snd c')).
Proof.
  induction 1; simpl; env_fix; use value_regular.
Qed.

(** Automation for reasoning on well-formedness. *)

Hint Extern 1 (ok ?E) =>
  match goal with
  | H: typing E _ _ _ |- _ => apply (proj1 (typing_regular H))
  end.

Hint Extern 1 (term ?t) =>
  match goal with
  | H: typing _ _ t _ |- _ => apply (proj2 (typing_regular H))
  | H: red (t,_) _ |- _ => apply (proj1 (proj1 (red_regular H)))
  | H: red _ (t,_) |- _ => apply (proj2 (proj1 (red_regular H)))
  | H: value t |- _ => apply (value_regular H)
  end.

Hint Extern 1 (sto_ok ?mu) =>
  match goal with
  | H: red (_,mu) _ |- _ => apply (proj1 (proj2 (red_regular H)))
  | H: red _ (_,mu) |- _ => apply (proj2 (proj2 (red_regular H)))
  | H: sto_typing _ mu |- _ => apply (proj1 H)
  end.

