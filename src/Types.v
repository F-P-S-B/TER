From Coq Require Import Unicode.Utf8.
Require Import Hints.
Require Maps.
Import Maps.Notations.
Require Import Syntax.

Definition context := @Maps.map type.
Definition empty := @Maps.empty type.




Inductive has_type : context -> expr -> type -> Prop := 
  (* Base λ-calculus *)
  | T_Var: 
      ∀ Γ x t, 
      Γ ? x = Some t -> 
      has_type Γ (E_Var x) t

  | T_Fun: 
      ∀ Γ x t1 e t2,
      has_type (x |-> t1; Γ) e t2 ->
      has_type Γ (E_Fun x t1 e) (Type_Fun t1 t2)

  | T_App: 
      ∀ Γ e1 e2 t1 t2, 
      has_type Γ e2 t1 -> 
      has_type Γ e1 (Type_Fun t1 t2) ->
      has_type Γ (E_App e1 e2) t2

  (* Booleans and conditions *)
  | T_True: 
      ∀ Γ, 
      has_type Γ E_True Type_Bool
              
  | T_False: 
      ∀ Γ, 
      has_type Γ E_False Type_Bool

  | T_If: 
      ∀ Γ e1 e2 e3 t, 
      has_type Γ e1 Type_Bool -> 
      has_type Γ e2 t -> 
      has_type Γ e3 t -> 
      has_type Γ (E_If e1 e2 e3) t 

  (* Let expressions *)
  | T_Let : 
      ∀ Γ x e1 e2 t1 t2, 
      has_type Γ e1 t1 -> 
      has_type (x |-> t1; Γ) e2 t2 -> 
      has_type Γ (E_Let x e1 e2) t2

  (* Arithmetic *)
  | T_Num : 
      ∀ Γ z, 
      has_type Γ (E_Num z) Type_Num 

  | T_Minus : 
      ∀ Γ e1 e2, 
      has_type Γ e1 Type_Num ->
      has_type Γ e2 Type_Num ->
      has_type Γ (E_Minus e1 e2) Type_Num 
    
  | T_Eq :
      ∀ Γ e1 e2, 
      has_type Γ e1 Type_Num ->
      has_type Γ e2 Type_Num ->
      has_type Γ (E_Eq e1 e2) Type_Bool 

  (* Pairs *)
  | T_Pair :
      ∀ Γ e₁ e₂ t₁ t₂, 
      has_type Γ e₁ t₁ ->
      has_type Γ e₂ t₂ ->
      has_type Γ (E_Pair e₁ e₂) (Type_Prod t₁ t₂) 
  | T_First :
      ∀ Γ e t₁ t₂,
      has_type Γ e (Type_Prod t₁ t₂) ->
      has_type Γ (E_First e) t₁
  | T_Second :
      ∀ Γ e t₁ t₂,
      has_type Γ e (Type_Prod t₁ t₂) ->
      has_type Γ (E_Second e) t₂

  (* Records *)
  | T_Record_Nil :
      ∀ Γ, has_type Γ E_Record_Nil Type_Record_Nil
  | T_Record_Cons :
      ∀ Γ x e tail t_e t_tail, 
      has_type Γ e t_e -> 
      has_type Γ tail t_tail -> 
      record_type t_tail -> 
      has_type Γ (E_Record_Cons x e tail) (Type_Record_Cons x t_e t_tail) 
  | T_Record_Access :
      ∀ Γ x e t_e t_acc, 
      has_type Γ e t_e -> 
      lookup_type_record x t_e = Some t_acc ->
      has_type Γ (E_Record_Access e x) t_acc
  
  | T_Fix :
      ∀ Γ e t, 
      has_type Γ e (Type_Fun t t) -> 
      has_type Γ (E_Fix e) t
.

Hint Constructors has_type : local_hints.

  
  
Local Lemma weakening : ∀ Γ Γ' e t, 
  Maps.includedin Γ Γ' ->
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


Local Lemma weakening_empty : ∀ Γ e t, 
  has_type empty e t ->
  has_type Γ e t.
Proof.
intros. apply (weakening empty); auto.
intros x v contra. discriminate contra.
Qed.

Hint Resolve weakening_empty : local_hints.
