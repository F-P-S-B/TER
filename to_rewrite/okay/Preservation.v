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

Lemma test1 : 
  ∀ Σ Γ constr v branches t s e,
  has_type Σ Γ (E_Sum_Match (E_Sum_Constr constr v) (LSE_Cons s e branches)) t -> 
  s ≠ constr -> 
  has_type Σ Γ (E_Sum_Match (E_Sum_Constr constr v) branches) t.
Proof. 
  Admitted.


Lemma test : 
  ∀ Σ Γ constr v branches t b,
  has_type Σ Γ (E_Sum_Match (E_Sum_Constr constr v) branches) t ->
  lookup_constr constr branches = Some b ->
  ∃ t_arg, 
      has_type Σ Γ v t_arg 
   /\ has_type Σ Γ b {{t_arg -> t}}.
Proof.
  intros.
  induction branches.
  - inversion H0.
  - simpl in H0.
    destruct (String.eqb_spec constr s); subst.
    + admit.
    + inversion H; subst. 
  Admitted.
  




(* Lemma test: 
  ∀ name_sum constr Σ Γ branches b t t_arg, 
  lookup_type_sum constr Σ = Some (name_sum, t_arg) ->
  lookup_constr constr branches = Some b ->
  has_type_lsexpr name_sum Σ Γ branches t ->
  has_type Σ Γ b {{t_arg -> t}}
.
Proof with eauto with local_hints.
  intros.
  induction branches.
  - inversion H0.
  - simpl in H0.
    destruct (String.eqb_spec constr s); subst.
    + inversion H0; subst.
      inversion H1; subst. 
      rewrite H in H10.
      inversion H10; subst...
    + inversion H1; subst. 
      apply IHbranches...
Qed. *)

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
    Check test.
    eapply test in H_type as [t_arg [H_t_v H_t_b]]...
    (* TODO: 
      Lemme sur le type des branches:
      t_a -> t 
      avec t_a le type associé au constructeur
      
    *)
Qed.