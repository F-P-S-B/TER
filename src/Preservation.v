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
  Σ / empty |- e : t  ->
  e --> e'  ->
  Σ / empty |- e' : t.
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
  clear e P P0;
  try (
    intros;
    match goal with 
    | [ H_step : _ -->ₗ _
        |- _] => 
          inversion H_step
    | [ H_type : has_type _ _ _ _,
        H_step : _ --> _
        |- _] => 
        inversion H_step; subst; 
          inversion H_type; subst;
          eauto 3 with local_hints;
          match goal with 
          | [ H : has_type _ _ <{ inr < _ | _ > _ }> _ |- _ ] => inversion H 
          | [ H : has_type _ _ <{ inl < _ | _ > _ }> _ |- _ ] => inversion H 
          | [ H : has_type _ _ _ _ |- _ ] => inversion H 
          | _ => idtac
          end; subst; eauto 3 with local_hints
    end; fail
  ).

  - intros * IH1 * H_type H_step.
    inversion H_step; subst;
    inversion H_type; subst...
    edestruct IH1...


  - intros * IH1 * IH2 * IH3 * H_type H_step.
    inversion H_step; subst;
    inversion H_type; subst;
    eauto 3 with local_hints;
    try (edestruct IH3; eauto 3 with local_hints; fail).
    match goal with 
    | [ H_t : has_type _ _ (E_Sum_Constr _ _) _ |- _] => 
        inversion H_t; subst; eauto 3 with local_hints
    end.

  
  - intros * IH1 * IH2 * H_step. split; intros * H_type;
    inversion H_step; subst;
    inversion H_type; subst; 
    eauto with local_hints;
    edestruct IH2...
Qed.