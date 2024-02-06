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




(* Theorem preservation : ∀ e e' t,
  has_type empty e t  ->
  step e e'  ->
  has_type empty e' t.
Proof.
  (* remember empty as Γ. *)
  (* induction e;
  intros * H_type_e H_step.
  - inversion H_type_e. discriminate H1.
  - inversion H_type_e; subst. 
    inversion H_step; subst; eauto with local_hints.
    inversion H4; subst.
    eapply Step.subst_typing; eauto.
  -   *)

  induction e; intros e' τ H_type H_step;
  try (inversion H_type; subst; 
    inversion H_step; subst;
    eauto with local_hints).
    - inversion H4. eauto with local_hints.
    - inversion H2; subst. 
      rewrite Maps.update_eq in H4. 
      inversion H4; subst. auto.
    - inversion H2; subst. 
      inversion H5; subst.
      + eapply T_Access.

    
Qed. *)

(* Theorem preservation : ∀ e e' t,
  has_type empty e t  ->
  step e e'  ->
  has_type empty e' t.
Proof.
  intros * H_type_e. 
  generalize dependent e'.
  remember empty as Γ.
  induction H_type_e;
  intros e' H_step; 
  try (
    inversion H_step; 
    subst; 
    eauto with local_hints).
  - inversion H_type_e2; subst. eauto with local_hints.
  - inversion H_type_e; subst. 
    inversion H. rewrite String.eqb_refl in H1. 
    inversion H1; subst. auto.
  - inversion H6; subst.
    + eapply Step.not_value in H4. exfalso. eauto.
    + admit.
    + 
Qed. *)