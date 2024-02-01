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


Theorem preservation : ∀ e e' t,
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
  - apply T_Rec.
    inversion H_step; subst.
    assert (Maps.same_bindings (x |-> e'0; m) (x |-> e; m)).
    {
      apply Maps.same_bindings_update.
      apply Maps.same_bindings_refl.
    }
    eapply Maps.same_bindings_trans; eauto.
Qed.

Theorem preservation' : ∀ e e' t,
  has_type empty e t  ->
  step e e'  ->
  has_type empty e' t.
Proof.
  induction e; intros e' τ H_type H_step;
  try (inversion H_type; subst; 
    inversion H_step; subst;
    eauto with local_hints).
    - inversion H4. eauto with local_hints.
    - apply T_Rec.
      inversion H_step; subst.
      assert (Maps.same_bindings (x |-> e'0; fields) fields).
      {
        eapply Maps.same_bindings_shadow_add.
        - apply Maps.same_bindings_refl.
        - apply H5. 
      }
      eapply Maps.same_bindings_trans; eauto.
Qed.