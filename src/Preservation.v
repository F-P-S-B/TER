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

(* Définis dans Types.v, ils ne sont pas nécessaires avant et ralentissent considérablement la recherche automatique de preuve  *)
Hint Resolve lookup_has_type : local_hints.
Hint Resolve lookup_branches_type_fun : local_hints.

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
      ∀ Σ (branches' : lsexpr),
        branches -->ₗ branches' -> (
          ∀ (name_sum : string) (t : type),
          Σ / empty |-ₛ name_sum ~> branches  : t  ->
          Σ / empty |-ₛ name_sum ~> branches' : t
        ) /\ (
          ∀ (t : lstype),
          Σ / empty |-ᵣ branches : t  ->
          Σ / empty |-ᵣ branches' : t
        ) 
  ).
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0;
  clear P P0;
  try (
    try (intros * IH1 * IH2 * IH3 * H_type H_step);
    try (intros * IH1 * IH2 * H_type H_step);
    try (intros * IH1 * H_type H_step);
    try (intros * H_type H_step);
    inversion H_step; subst;
    inversion H_type; subst; eauto 3 with local_hints; fail
  ).

  - intros * IH1 * IH2 * H_type H_step.
    inversion H_step; subst;
    inversion H_type; subst...
    inversion H6...

  - intros * IH1 * H_type H_step.
    inversion H_step; subst;
    inversion H_type; subst...
    inversion H4...

  - intros * IH1 * H_type H_step.
    inversion H_step; subst;
    inversion H_type; subst...
    inversion H4...

  - intros * IH1 * H_type H_step.
    inversion H_step; subst;
    inversion H_type; subst...
    apply IH1 with (Σ := Σ) in H0 as [_ H]...

  - intros * IH1 * H_type H_step. 
    inversion H_step; subst;
    inversion H_type; subst...
    inversion H5...

  - intros * IH1 * H_type H_step.
    inversion H_step; subst;
    inversion H_type; subst...
    inversion H2; subst...

  - intros * IH1 * IH2 * IH3 * H_type H_step.
    inversion H_step; subst;
    inversion H_type; subst;
    try inversion H7; subst...

  - intros * IH1 * IH2 * IH3 * H_type H_step.
    inversion H_step; subst;
    inversion H_type; subst...
    + eapply IH3 in H4 as [H _]...
    + inversion H8; subst... 

  - intros * H_step. inversion H_step.
  
  - intros * IH1 * IH2 * H_step. split; intros * H_type;
    inversion H_step; subst;
    inversion H_type; subst...
    + eapply TB_Cons...
      eapply IH2 in H4 as [H _]...
    + eapply TRec_Cons...
      eapply IH2 in H4 as [_ H]...
Qed.