From Coq Require Import Unicode.Utf8.
Require Import Hints.
Require Maps.
Import Maps.Notations.
Require Import Syntax.

Definition context := @Maps.map type.
Definition empty := @Maps.empty type.



Reserved Notation "Γ '⊢' e '∈' τ" (at level 70, right associativity).

Inductive has_type : context -> expr -> type -> Prop := 
  (* Base λ-calculus *)
  | T_Var: 
      ∀ Γ x t, 
      Γ ? x = Some t -> 
      (Γ ⊢ (E_Var x) ∈ t)

  | T_Fun: 
      ∀ Γ x t1 e (t2 : type),
      (x |-> t1; Γ) ⊢ e ∈ t2 ->
      Γ ⊢ (E_Fun x t1 e) ∈ (Type_Fun t1 t2)

  | T_App: 
      ∀ Γ e1 e2 t1 t2, 
      Γ ⊢ e2 ∈ t1 -> 
      Γ ⊢ e1 ∈ (Type_Fun t1 t2) ->
      Γ ⊢ (E_App e1 e2) ∈ t2

  (* Booleans and conditions *)
  | T_True: 
      ∀ Γ, 
      Γ ⊢ E_True ∈ Type_Bool
              
  | T_False: 
      ∀ Γ, 
      Γ ⊢ E_False ∈ Type_Bool

  | T_If: 
      ∀ Γ e1 e2 e3 t, 
      Γ ⊢ e1 ∈ Type_Bool -> 
      Γ ⊢ e2 ∈ t -> 
      Γ ⊢ e3 ∈ t -> 
      Γ ⊢ (E_If e1 e2 e3) ∈ t 

  (* Let expressions *)
  | T_Let : 
      ∀ Γ x e1 e2 t1 t2, 
      Γ ⊢ e1 ∈ t1 -> 
      (x |-> t1; Γ) ⊢ e2 ∈ t2 -> 
      Γ ⊢ (E_Let x e1 e2) ∈ t2

  (* Arithmetic *)
  | T_Num : 
      ∀ Γ z, 
      Γ ⊢ (E_Num z) ∈ Type_Num 

  | T_Minus : 
      ∀ Γ e1 e2, 
      Γ ⊢ e1 ∈ Type_Num ->
      Γ ⊢ e2 ∈ Type_Num ->
      Γ ⊢ (E_Minus e1 e2) ∈ Type_Num 
    
  | T_Eq :
      ∀ Γ e1 e2, 
      Γ ⊢ e1 ∈ Type_Num ->
      Γ ⊢ e2 ∈ Type_Num ->
      Γ ⊢ (E_Eq e1 e2) ∈ Type_Bool 

  (* Pairs *)
  | T_Pair :
      ∀ Γ e₁ e₂ t₁ t₂, 
      Γ ⊢ e₁ ∈ t₁ ->
      Γ ⊢ e₂ ∈ t₂ ->
      Γ ⊢ (E_Pair e₁ e₂) ∈ (Type_Prod t₁ t₂) 
  | T_First :
      ∀ Γ e t₁ t₂,
      Γ ⊢ e ∈ (Type_Prod t₁ t₂) ->
      Γ ⊢ (E_First e) ∈ t₁
  | T_Second :
      ∀ Γ e t₁ t₂,
      Γ ⊢ e ∈ (Type_Prod t₁ t₂) ->
      Γ ⊢ (E_Second e) ∈ t₂

  (* Records *)
  | T_Record_Nil :
      ∀ Γ, 
      Γ ⊢ E_Record_Nil ∈ Type_Record_Nil
  | T_Record_Cons :
      ∀ Γ x e tail t_e t_tail, 
      Γ ⊢ e ∈ t_e -> 
      Γ ⊢ tail ∈ t_tail -> 
      record_type t_tail -> 
      Γ ⊢ (E_Record_Cons x e tail) ∈ (Type_Record_Cons x t_e t_tail) 
  | T_Record_Access :
      ∀ Γ x e t_e t_acc, 
      Γ ⊢ e ∈ t_e -> 
      lookup_type_record x t_e = Some t_acc ->
      Γ ⊢ (E_Record_Access e x) ∈ t_acc
  
  | T_Fix :
      ∀ Γ e t, 
      Γ ⊢ e ∈ (Type_Fun t t) -> 
      Γ ⊢ (E_Fix e) ∈ t
  where
    "Γ '⊢' e '∈' τ" := (has_type Γ e τ)
.

Hint Constructors has_type : local_hints.

  
  
Local Lemma weakening : ∀ Γ Γ' e t, 
  Maps.includedin Γ Γ' ->
  Γ ⊢ e ∈ t ->
  Γ' ⊢ e ∈ t.
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


Local Lemma weakening_empty : ∀ Γ e t, 
  empty ⊢ e ∈ t ->
  Γ ⊢ e ∈ t.
Proof.
  intros. apply (weakening empty); auto.
  intros x v contra. discriminate contra.
Qed.

Hint Resolve weakening_empty : local_hints.
