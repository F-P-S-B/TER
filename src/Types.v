From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Maps.
Require Import Syntax.
Require Import Step.
Require Import Hints.

Definition context := @Maps.map type.
Definition empty := @Maps.empty type.


Inductive has_type : context -> expr -> type -> Prop := 
| T_Var: forall Γ x t, 
            Γ ? x = Some t -> 
            has_type Γ (E_Var x) t

| T_Fun: forall Γ x t1 e t2,
            has_type (x |-> t1; Γ) e t2 ->
            has_type Γ (E_Fun x t1 e) (Type_Fun t1 t2)
| T_App: forall Γ e1 e2 t1 t2, 
            has_type Γ e2 t1 -> 
            has_type Γ e1 (Type_Fun t1 t2) ->
            has_type Γ (E_App e1 e2) t2

| T_True: forall Γ, 
            has_type Γ E_True Type_Bool
| T_False: forall Γ, 
            has_type Γ E_True Type_Bool

| T_If: forall Γ e1 e2 e3 t, 
            has_type Γ e1 Type_Bool -> 
            has_type Γ e2 t -> 
            has_type Γ e3 t -> 
            has_type Γ (E_If e1 e2 e3) t 
| T_Let : forall Γ x e1 e2 t1 t2, 
            has_type Γ e1 t1 -> 
            has_type (x |-> t1; Γ) e2 t2 -> 
            has_type Γ (E_Let x e1 e2) t2
| T_Num : forall Γ z, has_type Γ (E_Num z) Type_Num 
| T_Minus : forall Γ e1 e2, 
              has_type Γ e1 Type_Num ->
              has_type Γ e2 Type_Num ->
              has_type Γ (E_Minus e1 e2) Type_Num 
.

Hint Constructors has_type : local_hints.


Local Lemma weakening : ∀ Γ Γ' e t, 
    includedin Γ Γ' ->
    has_type Γ e t ->
    has_type Γ' e t.
Proof.
    intros * H_included H_type.
    generalize dependent Γ'.
    induction H_type; intros; eauto with local_hints.
    - apply T_Fun. apply IHH_type.
      apply Maps.includedin_update. assumption.
    - eapply T_Let; eauto. 
      apply IHH_type2.
      apply Maps.includedin_update.
      assumption.
Qed.

Hint Resolve weakening : local_hints.


Lemma weakening_empty : ∀ Γ e t, 
    has_type empty e t ->
    has_type Γ e t.
Proof.
intros. apply (weakening empty); auto.
intros x v contra. discriminate contra.
Qed.

Hint Resolve weakening_empty : local_hints.