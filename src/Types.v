From Coq Require Import Unicode.Utf8.
Require Import Hints.
Require Maps.
Import Maps.Notations.
Require Import Syntax.

Definition context := @Maps.map type.
Definition empty := @Maps.empty type.

Inductive has_type : context -> expr -> type -> Prop := 
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

    | T_Let : 
        ∀ Γ x e1 e2 t1 t2, 
        has_type Γ e1 t1 -> 
        has_type (x |-> t1; Γ) e2 t2 -> 
        has_type Γ (E_Let x e1 e2) t2

    | T_Num : 
        ∀ Γ z, 
        has_type Γ (E_Num z) Type_Num 

    | T_Minus : 
        ∀ Γ e1 e2, 
        has_type Γ e1 Type_Num ->
        has_type Γ e2 Type_Num ->
        has_type Γ (E_Minus e1 e2) Type_Num 
    
    (* | T_Rec : 
        ∀ Γ m_fields m_types,
        Maps.same_bindings m_fields m_types -> 
        has_type Γ (E_Rec m_fields) (Type_Rec m_types) *)
    | T_Rec_Unit : 
        ∀ Γ,
        has_type Γ (E_Rec (@Maps.empty expr)) (Type_Rec empty) 
    | T_Rec_Rec : 
        ∀ Γ m_fields m_types x v t,
        has_type Γ v t ->
        has_type Γ (E_Rec m_fields) (Type_Rec m_types) ->
        has_type Γ 
            (E_Rec (x|-> v; m_fields)) 
            (Type_Rec (x |-> t; m_types)) 
    | T_Access :
        ∀ Γ e x t m_types,
        has_type Γ e (Type_Rec m_types) -> 
        m_types ? x = Some t -> 
        has_type Γ (E_Access e x) t
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
