From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Closed.
Require Import Hints.

Require Maps.
Import Maps.Notations.
Require Import Syntax.
Require Import Types.
Require Import List.
Import ListNotations.



(* TODO: voir si on repasse à une propriété inductive pour l'hypothèse s clos qui est nécessaire *)
Fixpoint sub  (s : expr) (x : string) (e: expr) := 
  match e with 
  | <{#y}> => if (x =? y)%string then s else e
  | <{ e₁ e₂}> => <{`sub s x e₁` `sub s x e₂`}>
  | <{fun y : t => e}> => 
      if (x =? y)%string 
      then <{fun y : t => e}>
      else <{fun y : t => `sub s x e`}>

  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{if e₁ then e₂ else e₃}> => <{if `sub s x e₁` then `sub s x e₂` else `sub s x e₃`}>
  
  | <{let y = e₁ in e₂}> =>
        if (x =? y)%string 
        then <{let y = `sub s x e₁` in e₂}>
        else <{let y = `sub s x e₁` in `sub s x e₂`}>

  | E_Num z => E_Num z
  | <{ e₁ - e₂}> => <{`sub s x e₁` - `sub s x e₂`}>
  | <{ e₁ == e₂}> => <{`sub s x e₁` == `sub s x e₂`}>

  | <{ (e₁, e₂)}> => <{(`sub s x e₁`, `sub s x e₂`)}>
  | <{first e}> => <{first `sub s x e`}>
  | <{second e}> => <{second `sub s x e`}>

  | <{ { lse } }> => <{ { `sub_lse s x lse` } }>
  | <{e::v}> => <{`sub s x e` :: v}>
  | <{fix e}> => <{fix `sub s x e`}>

  | <{inl <t₁ | t₂> e}> => <{inl <t₁ | t₂> `sub s x e`}>
  | <{inr <t₁ | t₂> e}> => <{inr <t₁ | t₂> `sub s x e`}>
  | <{match e with | inl => eₗ | inr => eᵣ end}> => <{
        match `sub s x e` with 
        | inl => `sub s x eₗ` 
        | inr => `sub s x eᵣ` 
        end
      }> 
  | <{ unit }> => <{ unit }>
  | E_Sum_Constr constr e => E_Sum_Constr constr (sub s x e)
  | <{match_sum e with branches : default end_sum}> => <{
        match_sum `sub s x e` with 
        `sub_lse s x branches` 
        : `sub s x default` 
        end_sum
      }> 
  end
  with 
    sub_lse (s : expr) (x : string) (lse : lsexpr) : lsexpr :=
      match lse with 
      | <{ nil }> => <{ nil }>
      | <{ y := e; tail }> => <{ y := `sub s x e` ; `sub_lse s x tail` }>
      end 
  .
Hint Unfold sub : local_hints.
Hint Unfold sub_lse : local_hints.

Local Theorem preserves_typing : 
  ∀ e Σ Γ s x tₑ tₛ, 
  Σ / empty |- s : tₛ -> 
  Σ / (x |-> tₛ; Γ) |- e : tₑ -> 
  Σ / Γ |- `sub s x e` : tₑ. 
Proof with eauto with local_hints.
  intro e.
  pose (
    P (e: expr) :=
      ∀ Σ Γ s x tₑ tₛ, 
    Σ / empty |- s : tₛ -> 
    Σ / (x |-> tₛ; Γ) |- e : tₑ -> 
    Σ / Γ |- `sub s x e` : tₑ
  ).
  pose (
    P0 (branches: lsexpr) :=
      ∀ Σ Γ s x tₛ,
      Σ / empty |- s : tₛ -> 
      (
        ∀ name_sum t,
        Σ / (x |-> tₛ; Γ) |-ₛ name_sum ~> branches : t -> 
        Σ / Γ |-ₛ name_sum ~> `sub_lse s x branches` : t
      ) /\ (
        ∀ t,
        Σ / (x |-> tₛ; Γ) |-ᵣ branches : t -> 
        Σ / Γ |-ᵣ `sub_lse s x branches` : t
      )
  ).

  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0;
  clear P P0;
  try (
    intros * IH1 * IH2 * IH3 * H_type_s H_type_e;
    inversion H_type_e; subst;
    eauto with local_hints;
    fail
  );
  try (
    intros * IH1 * IH2 * H_type_s H_type_e;
    inversion H_type_e; subst;
    eauto with local_hints;
    fail
  );
  try (
    intros * IH * H_type_s H_type_e;
    inversion H_type_e; subst;
    eauto with local_hints;
    fail
  );
  try (
    intros * H_type_s H_type_e ;
    inversion H_type_e; subst;
    eauto with local_hints;
    fail
  ).
  - intros * H_type_s H_type_e.
    inversion H_type_e; subst.
    destruct (String.eqb_spec x0 x).
    + subst. inversion H2. simpl. rewrite String.eqb_refl in *. 
      inversion H0; subst...
    + simpl. rewrite <- String.eqb_neq in n. inversion H2. rewrite n in *...
  - intros * IH1 * H_type_s H_type_e.
    inversion H_type_e; subst.
    simpl.
    destruct (String.eqb_spec x0 x).
    + apply T_Fun; subst.
      apply Types.weakening_eq with (Γ₁ := (x |-> t; x |-> tₛ; Γ))...
      apply Maps.update_shadow.
    + apply T_Fun.
      assert (has_type Σ (x0 |-> tₛ; x |-> t; Γ) e0 t₂) 
      by (
        apply Types.weakening_eq with (x |-> t; x0 |-> tₛ; Γ);
        try apply Maps.update_permute; eauto with local_hints
      )...
  - intros * IH1 * IH2 * H_type_s H_type_e.
    inversion H_type_e; subst.
    simpl.
    destruct (String.eqb_spec x0 x).
    + eapply T_Let; subst.
      * eapply IH1...
      * apply Types.weakening_eq with ((x |-> t₁; x |-> tₛ; Γ))...
        apply Maps.update_shadow...
    + eapply T_Let.
      * eapply IH1...
      * assert (has_type Σ (x0 |-> tₛ; x |-> t₁; Γ) e2 tₑ)
        by (
          apply Types.weakening_eq with (x |-> t₁; x0 |-> tₛ; Γ);
          try apply Maps.update_permute; eauto with local_hints
        )...  
  - intros * IH1 * H_type_s H_type_e.
    simpl.
    inversion H_type_e; subst.
    apply T_Recordt.
    destruct (IH1 Σ Γ s x tₛ H_type_s) as [_ IH]...
  - intros * IH1 * IH2 * IH3 * H_type_s H_type_e.
    inversion H_type_e.
    destruct (IH3 Σ Γ s x tₛ H_type_s) as [IH2_rec IH2_sum]...
  - intros * H_type_s.
    split; intros * H_type_nil...
    inversion H_type_nil... 
  - intros * IH1 * IH2 * H_type_s.
    split; intros * H_type_cons; simpl;
    inversion H_type_cons; subst;
    destruct (IH2 Σ Γ s0 x tₛ H_type_s) as [IH2_rec IH2_sum]...
Qed.
Hint Resolve preserves_typing : local_hints.
