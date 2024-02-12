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
.

Hint Constructors substitution : local_hints.

Local Lemma exists_one : ∀ s x e, closed s -> ∃ e', 
substitution s x e e'.
Proof with eauto with local_hints.
  intros.
  induction e;
  try destruct IHe;
  try destruct IHe1;
  try destruct IHe2; 
  try destruct IHe3; 
  try destruct (String.eqb_spec x x0); 
  subst;
  eauto with local_hints.
Qed.

Hint Resolve exists_one : local_hints.
Search (_ = _ -> S _ = S _).

Local Theorem deterministic :
  ∀ s x e e'₁ e'₂, 
  substitution s x e e'₁ ->
  substitution s x e e'₂ ->
  e'₁ = e'₂.
Proof with eauto with local_hints.
  intros s x e.
  generalize dependent s.
  generalize dependent x.
  induction e; 
  intros * H_s_1 H_s_2; 
  inversion H_s_1; inversion H_s_2; subst;
  try contradiction;
  f_equal;
  eauto with local_hints.
Qed.

Local Lemma subst_typing : ∀ Γ s x e e' t_e t_s, 
  (x |-> t_s; Γ) ⊢ e ∈ t_e ->
  empty ⊢ s ∈ t_s ->
  substitution s x e e' -> 
  Γ ⊢ e' ∈ t_e.
Proof.
  intros * H_type_e H_type_s H_subst.
  generalize dependent t_e.
  generalize dependent t_s.
  generalize dependent Γ.
  induction H_subst; intros;
  try (inversion H_type_e; subst; eauto with local_hints; fail).
  - inversion H_type_e; subst. 
    rewrite Maps.update_eq in H1. inversion H1; subst. apply Types.weakening_empty.
    assumption.
  - inversion H_type_e; subst. 
    apply T_Var. rewrite Maps.update_neq in H2; auto.
  - inversion H_type_e; subst.
    apply T_Fun.   
    rewrite Maps.update_shadow in H4. assumption.    
  - inversion H_type_e; subst.
    apply T_Fun.
    rewrite Maps.update_permute in H6; auto.
    eapply IHH_subst; eauto.

  - inversion H_type_e; subst. eapply T_Let; eauto.
        rewrite Maps.update_shadow in H5. auto.
  - inversion H_type_e; subst. eapply T_Let; eauto.
    rewrite Maps.update_permute in H7; auto.
    eapply IHH_subst2; eauto.        
Qed.

Hint Resolve subst_typing : local_hints.
