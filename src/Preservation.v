From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Hints.
Require Import Syntax.
Require Import Types.
Require Import Subst.
Require Import Step.
Require Import Canonical_form.
Require Maps.
Import Maps.Notations.


Theorem preservation : 
  ∀ e Σ e' t,
  has_type Σ empty e t  ->
  e --> e'  ->
  has_type Σ empty e' t.
Proof with eauto 3 with local_hints.
  intro e.
  pose (
    P (e: expr) :=
      ∀ Σ e' t,
        has_type Σ empty e t  ->
        e --> e'  ->
        has_type Σ empty e' t
  ).
  pose (
    P0 (branches: lsexpr) :=
      ∀ name_sum Σ branches' t,
        has_type_lsexpr name_sum Σ empty branches t  ->
        branches -->ₗ branches'  ->
        has_type_lsexpr name_sum Σ empty branches' t
  ).
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0;
  clear P P0;
  try (intros * IH1 * IH2 * IH3 * H_type H_step);
  try (intros * IH1 * IH2 * H_type H_step);
  try (intros * IH * H_type H_step);
  try (intros * H_type H_step);
  try (inversion H_step; fail);
  try (inversion H_step; subst;
    inversion H_type; subst; eauto 3 with local_hints; fail).
  - inversion H_step; subst;
    inversion H_type; subst; 
    try (eapply T_App; eauto with local_hints; fail).
    inversion H7; subst.
    eapply Subst.preserves_typing...
  - inversion H_step; subst;
    inversion H_type; subst...
    inversion H4...
  - inversion H_step; subst;
    inversion H_type; subst...
    inversion H4...
  - inversion H_step; subst.
    + inversion H_type; subst.
      apply T_Fix...
    + inversion H_type; subst.
      inversion H3; subst...
  - inversion H_step; subst;
    inversion H_type; subst...
    all: inversion H7... 
  - inversion H_step; subst;
    inversion H_type; subst...
    (* TODO: 
      Lemme sur le type des branches:
      t_a -> t 
      avec t_a le type associé au constructeur
      
    *)
Qed.