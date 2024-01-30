From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Hints.
Require Import Syntax.
Require Import Types.
Require Import Subst.
Require Maps.
Import Maps.Notations.

Inductive step : expr -> expr -> Prop := 
    | ST_App_Fun : 
        ∀ (x : string) (t : type) (e e' v : expr),
        value v -> 
        substitution v x e e' ->
        step (E_App (E_Fun x t e) v) e'
    | ST_App_Left : 
        ∀ (e1 e1' e2 : expr),
        step e1 e1' ->
        step (E_App e1 e2) (E_App e1' e2)
    | ST_App_Right : 
        ∀ (v1 e2 e2' : expr),
        value v1 ->
        step e2 e2' ->
        step (E_App v1 e2) (E_App v1 e2')
    | ST_If_True : 
        ∀ (e1 e2 : expr),
        step (E_If E_True e1 e2) e1
    | ST_If_False : 
        ∀ (e1 e2 : expr),
        step (E_If E_False e1 e2) e2
    | ST_If : 
        ∀ (e1 e1' e2 e3 : expr),
        step e1 e1' ->
        step (E_If e1 e2 e3) (E_If e1' e2 e3)
    | ST_Let_Left : 
        ∀ (x : string) (e1 e1' e2 : expr),
        step e1 e1' ->
        step (E_Let x e1 e2) (E_Let x e1' e2)
    | ST_Let_Right : 
        ∀ (x : string) (v1 e2 e2' : expr),
        value v1 ->
        substitution v1 x e2 e2' ->
        step (E_Let x v1 e2) e2'
    | ST_Minus_Left :  
        ∀ (e1 e1' e2 : expr),
        step e1 e1' ->
        step (E_Minus e1 e2) (E_Minus e1' e2)
    | ST_Minus_Right :  
        ∀ (v1 e2 e2' : expr),
        value v1 ->
        step e2 e2' ->
        step (E_Minus v1 e2) (E_Minus v1 e2')
    | ST_Minus_Num : 
        ∀ (z1 z2 : Z),
        step 
            (E_Minus (E_Num z1) (E_Num z2))
            (E_Num (z1 - z2))
.

Hint Constructors step : local_hints.


Local Lemma subst_typing : ∀ Γ s x e e' t_e t_s, 
    has_type (x |-> t_s; Γ) e t_e ->
    has_type empty s t_s ->
    substitution s x e e' -> 
    has_type Γ e' t_e.
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
