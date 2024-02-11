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
  empty ⊢ e ∈ t  ->
  e ->> e'  ->
  empty ⊢ e' ∈ t.
Proof.
  intros * H_type_e. 
  generalize dependent e'.
  remember empty as Γ.
  induction H_type_e;   
  intros e' H_step;  
  try (
    inversion H_step; 
    subst; 
    try inversion H_type_e; subst;
    try inversion H_type_e2; subst;
    eauto with local_hints; fail
  ).
Qed.
