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


Inductive substitution (s : expr) (x : string) : expr -> expr -> Prop :=
  | S_Var_Eq :
      substitution s x (E_Var x) s
  | S_Var_Neq :
      ∀ (y : string), x <> y -> substitution s x (E_Var y) (E_Var y)
  | S_App : 
      ∀ (e1 e1' e2 e2' : expr),
      substitution s x e1 e1' ->
      substitution s x e2 e2' ->
      substitution s x (E_App e1 e2) (E_App e1' e2')
  | S_Fun_Eq : 
      ∀ (t : type) (e : expr),
      substitution s x (E_Fun x t e) (E_Fun x t e)
  | S_Fun_Neq : 
      ∀ (y: string) (t : type) (e e' : expr),
      x <> y ->
      closed s ->
      substitution s x e e' -> 
      substitution s x (E_Fun y t e) (E_Fun y t e')
  | S_True : 
      substitution s x E_True E_True
  | S_False : 
      substitution s x E_False E_False
  | S_If : 
      ∀ (e1 e1' e2 e2' e3 e3' : expr),
      substitution s x e1 e1' ->
      substitution s x e2 e2' ->
      substitution s x e3 e3' ->
      substitution s x (E_If e1 e2 e3) (E_If e1' e2' e3')
  | S_Let_Eq : 
      ∀ (e1 e1' e2 : expr),
      substitution s x e1 e1' -> 
      substitution s x (E_Let x e1 e2) (E_Let x e1' e2)
  | S_Let_Neq : 
      ∀ (y : string) (e1 e1' e2 e2': expr),
      x <> y ->
      closed s ->
      substitution s x e1 e1' -> 
      substitution s x e2 e2' -> 
      substitution s x (E_Let y e1 e2) (E_Let y e1' e2')
  
  | S_Num : 
      ∀ (z : Z),
      substitution s x (E_Num z) (E_Num z)
  | S_Minus :
      ∀ (e1 e1' e2 e2': expr),
      substitution s x e1 e1' -> 
      substitution s x e2 e2' -> 
      substitution s x (E_Minus e1 e2) (E_Minus e1' e2')

  | S_Eq :
      ∀ (e1 e1' e2 e2': expr),
      substitution s x e1 e1' -> 
      substitution s x e2 e2' -> 
      substitution s x (E_Eq e1 e2) (E_Eq e1' e2')
  
  | S_Pair : 
      ∀ (e1 e1' e2 e2': expr),
      substitution s x e1 e1' -> 
      substitution s x e2 e2' -> 
      substitution s x (E_Pair e1 e2) (E_Pair e1' e2')
  | S_First :
      ∀ (e e': expr),
      substitution s x e e' -> 
      substitution s x (E_First e) (E_First e')
  | S_Second :
      ∀ (e e': expr),
      substitution s x e e' -> 
      substitution s x (E_Second e) (E_Second e')

  | S_Record_Nil : 
      substitution s x E_Record_Nil E_Record_Nil
    
  | S_Record_Cons :
    ∀ y e e' tail tail',
    substitution s x tail tail' ->
    substitution s x e e' ->
    substitution s x (E_Record_Cons y e tail) (E_Record_Cons y e' tail')
  
  | S_Record_Access :
    ∀ y e e',
    substitution s x e e' ->
    substitution s x (E_Record_Access e y) (E_Record_Access e' y)

  | S_Fix :
    ∀ e e',
    substitution s x e e' -> 
    substitution s x (E_Fix e) (E_Fix e')

  | S_In_Left :
      ∀ t₁ t₂ e e', 
      substitution s x e e' ->
      substitution s x (E_In_Left t₁ t₂ e) (E_In_Left t₁ t₂ e')
  
  | S_In_Right :
      ∀ t₁ t₂ e e', 
      substitution s x e e' ->
      substitution s x (E_In_Right t₁ t₂ e) (E_In_Right t₁ t₂ e')

  | S_Match :
      ∀ e₁ e₂ e₃ e₁' e₂' e₃', 
      substitution s x e₁ e₁' ->
      substitution s x e₂ e₂' ->
      substitution s x e₃ e₃' ->
      substitution s x (E_Match e₁ e₂ e₃) (E_Match e₁' e₂' e₃')

  | S_Unit : substitution s x E_Unit E_Unit
  
  | S_Sum_Constr :
      ∀ constr e e',
      substitution s x e e' ->
      substitution s x (E_Sum_Constr constr e) (E_Sum_Constr constr e')

  | S_Sum_Match :
      ∀ e e' branches branches',
      substitution s x e e' ->
      substitution_lsexpr s x branches branches' -> 
      substitution s x
        (E_Sum_Match e branches) 
        (E_Sum_Match e' branches')
  
  (* | S_Expr : ∀ exc, substitution s x (E_Exception exc) (E_Exception exc) *)

with substitution_lsexpr (s : expr) (x : string) : lsexpr -> lsexpr -> Prop :=
  | S_LSExpr_Nil : substitution_lsexpr s x LSE_Nil LSE_Nil
  | S_LSExpr_Cons :
    ∀ constr e e' branches branches', 
    substitution s x e e' ->
    substitution_lsexpr s x branches branches' ->
    substitution_lsexpr s x 
      (LSE_Cons constr e branches)
      (LSE_Cons constr e' branches')
.

Hint Constructors substitution : local_hints.
Hint Constructors substitution_lsexpr : local_hints.

Check expr_ind.

Fixpoint lookup_constr (constr : string) (branches : lsexpr) : option expr :=
  match branches with
  | LSE_Nil => None
  | LSE_Cons constr' e tail =>
      if (constr =? constr')%string 
      then Some e 
      else lookup_constr constr tail
  end.


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
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0; intros;
  try (
    try destruct H0; 
    try destruct H1; 
    try destruct H2;
    try destruct (String.eqb_spec x x0); subst; 
    eauto with local_hints; 
    fail
  ).
Qed.

Hint Resolve exists_one : local_hints.
Search (_ = _ -> S _ = S _).

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

  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0;
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
  ∀ e Γ Σ s x e' t_e t_s, 
  has_type Σ (x |-> t_s; Γ)  e  t_e -> 
  has_type Σ empty  s  t_s -> 
  substitution s x e e' -> 
  has_type Σ Γ e' t_e. 
Proof with eauto with local_hints.
  intro e.
  pose (
    P (e: expr) :=
      ∀ Γ Σ s x e' t_e t_s, 
      has_type Σ (x |-> t_s; Γ)  e  t_e -> 
      has_type Σ empty  s  t_s -> 
      substitution s x e e' -> 
      has_type Σ Γ e' t_e
  ).
  pose (
    P0 (branches: lsexpr) :=
      ∀ name_sum Γ Σ s x branches' t_branches t_s, 
      has_type_lsexpr name_sum Σ (x |-> t_s; Γ) branches t_branches -> 
      has_type Σ empty s t_s -> 
      substitution_lsexpr s x branches branches' -> 
      has_type_lsexpr name_sum Σ Γ branches' t_branches
  ).

  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0;
  clear P P0;
  try (
    intros * H_type_e H_type_s H_subst;
    inversion H_subst; inversion H_type_e; subst;
    eauto with local_hints;
    fail
  );
  try (
    intros * IH * H_type_e H_type_s H_subst;
    inversion H_subst; inversion H_type_e; subst;
    eauto with local_hints;
    fail
  );
  try (
    intros * IH1 * IH2 * H_type_e H_type_s H_subst;
    inversion H_subst; inversion H_type_e; subst;
    eauto with local_hints;
    fail
  );
  try (
    intros * IH1 * IH2 * IH3 * H_type_e H_type_s H_subst;
    inversion H_subst; inversion H_type_e; subst;
    eauto with local_hints;
    fail
  ).
  - intros * H_type_e H_type_s H_subst.
    inversion H_subst;
    inversion H_type_e; inversion H4; subst.
    + rewrite String.eqb_refl in *. inversion H7; subst...
    + apply T_Var. rewrite <- H5. symmetry; apply Maps.update_neq...
  - intros * IH * H_type_e H_type_s H_subst.
    inversion H_subst;
    inversion H_type_e; subst.
    + apply T_Fun.
      apply Types.weakening_eq with (Γ₁ := (x |-> t; x |-> t_s; Γ))...
      apply Maps.update_shadow.
    + apply T_Fun.
      assert (has_type Σ (x0 |-> t_s; x |-> t; Γ) e0 t2) 
      by (
        apply Types.weakening_eq with (x |-> t; x0 |-> t_s; Γ);
        try apply Maps.update_permute; eauto with local_hints
      )...
  - intros * IH1 * IH2 * H_type_e H_type_s H_subst.
    inversion H_subst;
    inversion H_type_e; subst.
    + eapply T_Let.
      * eapply IH1...
      * apply Types.weakening_eq with ((x |-> t1; x |-> t_s; Γ));
        try apply Maps.update_shadow...
    + eapply T_Let.
      * eapply IH1...
      * assert (has_type Σ (x0 |-> t_s; x |-> t1; Γ) e2 t_e)
        by (
          apply Types.weakening_eq with (x |-> t1; x0 |-> t_s; Γ);
          try apply Maps.update_permute; eauto with local_hints
        )...  
Qed.
Hint Resolve preserves_typing : local_hints.
