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
Inductive substitution  (s : expr) (x : string) : expr -> expr -> Prop := 
  | S_Var_Eq :
      substitution s x <{ #x }> s
  | S_Var_Neq :
      ∀ (y : string), x <> y -> substitution s x <{ #y }>  <{ #y }>

  | S_App : 
      ∀ (e₁ e₁' e₂ e₂' : expr),
      substitution s x e₁ e₁' ->
      substitution s x e₂ e₂' ->
      substitution s x <{ e₁ e₂ }> <{ e₁' e₂' }>
  | S_Fun_Eq : 
      ∀ (t : type) (e : expr),
      substitution s x <{ fun x : t => e }> <{ fun x : t => e}>
      
  | S_Fun_Neq : 
      ∀ (y: string) (t : type) (e e' : expr),
      x <> y ->
      closed s ->
      substitution s x e e' -> 
      substitution s x <{ fun y : t => e }> <{ fun y : t => e'}>

  | S_True : 
      substitution s x <{ true }> <{ true }>
  | S_False : 
      substitution s x <{ false }> <{ false }>
  | S_If : 
      ∀ (e₁ e₁' e₂ e₂' e₃ e₃' : expr),
      substitution s x e₁ e₁' ->
      substitution s x e₂ e₂' ->
      substitution s x e₃ e₃' ->
      substitution s x 
        <{ if e₁ then e₂ else e₃ }> 
        <{ if e₁' then e₂' else e₃' }>

  | S_Let_Eq : 
      ∀ (e₁ e₁' e₂ : expr),
      substitution s x e₁ e₁' -> 
      substitution s x 
        <{let x = e₁  in e₂ }>
        <{let x = e₁' in e₂ }>
      
  | S_Let_Neq : 
      ∀ (y : string) (e₁ e₁' e₂ e₂': expr),
      x <> y ->
      closed s ->
      substitution s x e₁ e₁' -> 
      substitution s x e₂ e₂' -> 
      substitution s x 
        <{let y = e₁  in e₂  }>
        <{let y = e₁' in e₂' }>

  | S_Num : 
      ∀ (z : Z),
      substitution s x <{ z }> <{ z }>

  | S_Minus :
      ∀ (e₁ e₁' e₂ e₂': expr),
      substitution s x e₁ e₁' -> 
      substitution s x e₂ e₂' -> 
      substitution s x <{ e₁ - e₂ }> <{ e₁' - e₂' }>

  | S_Eq :
      ∀ (e₁ e₁' e₂ e₂': expr),
      substitution s x e₁ e₁' -> 
      substitution s x e₂ e₂' -> 
      substitution s x <{ e₁ == e₂ }> <{ e₁' == e₂' }>
  
  | S_Pair : 
      ∀ (e₁ e₁' e₂ e₂': expr),
      substitution s x e₁ e₁' -> 
      substitution s x e₂ e₂' -> 
      substitution s x <{ (e₁, e₂) }> <{ (e₁', e₂') }>
  | S_First :
      ∀ (e e': expr),
      substitution s x e e' -> 
      substitution s x <{ first e }> <{ first e' }>
  | S_Second :
      ∀ (e e': expr),
      substitution s x e e' -> 
      substitution s x <{ second e }> <{ second e' }>

  | S_Records :
      ∀ lse lse',
      substitution_lsexpr s x lse lse' -> 
      substitution s x <{ { lse } }> <{ { lse' } }>

  | S_Record_Access :
      ∀ y e e',
      substitution s x e e' ->
      substitution s x <{ e::y }> <{ e'::y }>

  | S_Fix :
    ∀ e e',
    substitution s x e e' -> 
    substitution s x <{ fix e }> <{ fix e' }>

  | S_In_Left :
      ∀ t₁ t₂ e e', 
      substitution s x e e' ->
      substitution s x 
        <{ inl < t₁ | t₂ > e  }> 
        <{ inl < t₁ | t₂ > e' }>
      
  
  | S_In_Right :
      ∀ t₁ t₂ e e', 
      substitution s x e e' ->
      substitution s x 
        <{ inr < t₁ | t₂ > e  }> 
        <{ inr < t₁ | t₂ > e' }>

  | S_Match :
      ∀ e₁ e₂ e₃ e₁' e₂' e₃', 
      substitution s x e₁ e₁' ->
      substitution s x e₂ e₂' ->
      substitution s x e₃ e₃' ->
      substitution s x 
        <{ match e₁  with | inl => e₂  | inr => e₃  end }>
        <{ match e₁' with | inl => e₂' | inr => e₃' end }>
      

  | S_Unit : substitution s x <{ unit }> <{ unit }>
  
  | S_Sum_Constr :
      ∀ constr e e',
      substitution s x e e' ->
      substitution s x (E_Sum_Constr constr e) (E_Sum_Constr constr e')

  | S_Sum_Match :
      ∀ (e e' default default' : expr) (branches branches' : lsexpr),
      substitution s x e e' ->
      substitution s x default default' ->
      substitution_lsexpr s x branches branches' -> 
      substitution s x
        <{ match_sum e  with branches  : default  end_sum }>
        <{ match_sum e' with branches' : default' end_sum }>
  with 
    substitution_lsexpr (s : expr) (x : string) : lsexpr -> lsexpr -> Prop :=
      | S_LSExpr_Nil : substitution_lsexpr s x <{ nil }> <{ nil }>
      | S_LSExpr_Cons :
        ∀ y e e' branches branches', 
        substitution s x e e' ->
        substitution_lsexpr s x branches branches' ->
        substitution_lsexpr s x 
          <{ y := e  ; branches  }>
          <{ y := e' ; branches' }>
  .
Hint Constructors substitution : local_hints.
Hint Constructors substitution_lsexpr : local_hints.

Local Lemma exists_one : 
  ∀ e s x, closed s -> 
  ∃ e', substitution s x e e'.
Proof with eauto with local_hints.
  intros.
  pose (
    P (e : expr) :=
      ∃ e', substitution s x e e'
  ).
  pose (
    P0 (branches : lsexpr) :=
      ∃ branches', substitution_lsexpr s x branches branches'
  ).
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0; clear P; clear P0; intros;
  try (
    try destruct H0; 
    try destruct H1; 
    try destruct H2;
    try destruct (String.eqb_spec x x0); subst; 
    eauto with local_hints; 
    fail
  ).
Qed.


Local Theorem deterministic :
  ∀ e s x e'₁ e'₂, 
  substitution s x e e'₁ ->
  substitution s x e e'₂ ->
  e'₁ = e'₂.
Proof.
  intro e.
  pose (
    P (e: expr) :=
      ∀ s x e'₁ e'₂, 
        substitution s x e e'₁ ->
        substitution s x e e'₂ ->
        e'₁ = e'₂
  ).
  pose (
    P0 (branches: lsexpr) :=
      ∀ s x branches'₁ branches'₂, 
        substitution_lsexpr s x branches branches'₁ ->
        substitution_lsexpr s x branches branches'₂ ->
        branches'₁ = branches'₂
  ).

  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0; clear P P0;
  try (
    intros * H_s_1 H_s_2; inversion H_s_1; inversion H_s_2; subst;
    eauto with local_hints;
    try contradiction;
    f_equal;
    eapply IH; eauto with local_hints;
    fail
  );
  try (
    intros * IH * H_s_1 H_s_2; inversion H_s_1; inversion H_s_2; subst;
    eauto with local_hints;
    try contradiction;
    f_equal;
    eapply IH; eauto with local_hints;
    fail
  );
  try (
    intros * IH1 * IH2 * H_s_1 H_s_2; 
    inversion H_s_1; inversion H_s_2; subst; 
    eauto with local_hints;
    try contradiction;
    f_equal;
    try (eapply IH1; eauto with local_hints; fail);
    try (eapply IH2; eauto with local_hints; fail);
    fail
  );
  try (
    intros * IH1 * IH2 * IH3 * H_s_1 H_s_2; 
    inversion H_s_1; inversion H_s_2; subst;
    eauto with local_hints;
    try contradiction; 
    f_equal;
    try (eapply IH1; eauto with local_hints; fail);
    try (eapply IH2; eauto with local_hints; fail);
    try (eapply IH3; eauto with local_hints; fail);
    fail
  ).
Qed.


Local Theorem preserves_typing : 
  ∀ e Σ Γ s x e' tₑ tₛ, 
  Σ / empty |- s : tₛ -> 
  Σ / (x |-> tₛ; Γ) |- e : tₑ -> 
  substitution s x e e' ->
  Σ / Γ |- e' : tₑ. 
Proof with eauto with local_hints.
  intro e.
  pose (
    P (e: expr) :=
      ∀ Σ Γ s x e' tₑ tₛ, 
      Σ / empty |- s : tₛ -> 
      Σ / (x |-> tₛ; Γ) |- e : tₑ -> 
      substitution s x e e' ->
      Σ / Γ |- e' : tₑ
  ).
  pose (
    P0 (branches: lsexpr) :=
      ∀ Σ Γ s x branches' tₛ,
      Σ / empty |- s : tₛ -> 
      substitution_lsexpr s x branches branches' ->
      (
        ∀ name_sum t,
        Σ / (x |-> tₛ; Γ) |-ₛ name_sum ~> branches : t -> 
        Σ / Γ |-ₛ name_sum ~> branches' : t
      ) /\ (
        ∀ t,
        Σ / (x |-> tₛ; Γ) |-ᵣ branches : t -> 
        Σ / Γ |-ᵣ branches' : t
      )
  ).

  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0;
  clear P P0.
  24 : {
    intros * IH1 * IH2 * H_type_s H_subst.
    split;
    intros * H_type_e.
    - inversion H_type_e; subst. 
      inversion H_subst; subst.
      eapply TB_Cons.
      + destruct (IH2 Σ Γ s0 x branches'0 tₛ)...
      + eassumption.
      + eapply IH1...
    - inversion H_type_e; subst. 
      inversion H_subst; subst.
      eapply TRec_Cons.
      + destruct (IH2 Σ Γ s0 x branches'0 tₛ)...
      + eapply IH1...
  }
  23 : {
    intros * H_type_s H_subst.
    split; intros * H_type_nil.
    - inversion H_subst; subst...
    - inversion H_subst; subst.
      inversion H_type_nil; subst...
  }
  all:
  try (
    try intros * IH1 * IH2 * IH3 * H_type_s H_type_e H_subst;
    try (intros * IH1 * IH2 * H_type_s H_subst; split; intros * H_type_s);
    try intros * IH1 * IH2 * H_type_s H_type_e H_subst;
    try intros * IH1 * H_type_s H_type_e H_subst;
    try intros * H_type_s H_type_e H_subst
  );
  try (
    inversion H_type_e; subst;
    inversion H_subst; subst;
    eauto 3 with local_hints;
    fail
  ).
  - inversion H_type_e; subst.
    inversion H_subst; subst;
    simpl in *.
    + rewrite String.eqb_refl in *.
      inversion H2; subst...
    + simpl. rewrite <- String.eqb_neq in H0. inversion H2. rewrite H0 in *...
  - inversion H_type_e; subst;
    inversion H_subst; subst.
    eapply T_App.
    + eapply IH2...
    + eapply IH1...
  - inversion H_type_e; subst;
    inversion H_subst; subst.
    + apply T_Fun; subst.
      apply Types.weakening_eq with (Γ₁ := (x |-> t; x |-> tₛ; Γ))...
      apply Maps.update_shadow.
    + apply T_Fun.
      assert (has_type Σ (x0 |-> tₛ; x |-> t; Γ) e0 t₂) 
      by (
        apply Types.weakening_eq with (x |-> t; x0 |-> tₛ; Γ);
        try apply Maps.update_permute; eauto with local_hints
      )...
  - inversion H_type_e; subst;
    inversion H_subst; subst.
    eapply T_If.
    + eapply IH1...
    + eapply IH2...
    + eapply IH3...
  - inversion H_type_e; subst;
    inversion H_subst; subst.
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
        ).
        eapply IH2...  
  - inversion H_type_e; subst;
    inversion H_subst; subst.
    apply T_Minus.
    + eapply IH1...
    + eapply IH2...
  
  - inversion H_type_e; subst;
    inversion H_subst; subst.
    apply T_Eq.
    + eapply IH1...
    + eapply IH2...

  - inversion H_type_e; subst;
    inversion H_subst; subst.
    apply T_Pair.
    + eapply IH1...
    + eapply IH2...

  - inversion H_type_e; subst;
    inversion H_subst; subst.
    apply T_Recordt.
    destruct (IH1 Σ Γ s x lse' tₛ H_type_s) as [_ IH]...

  - inversion H_type_e; subst;
    inversion H_subst; subst.
    eapply T_Match.
    + eapply IH1...
    + eapply IH2...
    + eapply IH3...

  - inversion H_type_e; subst;
    inversion H_subst; subst.
    destruct (IH3 Σ Γ s x branches' tₛ H_type_s H8) as [IH3' _].
    eapply T_Sum_Match.
    + eapply IH1... 
    + eapply IH2...
    + eapply IH3'...
Qed.
Hint Resolve preserves_typing : local_hints.
