From Coq Require Import Unicode.Utf8.
Require Import Hints.
Require Maps.
Import Maps.Notations.
Require Import Syntax.
Require Import String.
Require Import List.
Import ListNotations.



Definition context := @Maps.map type.
Definition empty := @Maps.empty type.
Definition sum_types_constructors : Set := 
    list (string * list (type * string)).

Fixpoint lookup_type_constrs (constr : string) (constrs : list (type * string)) : option type := 
    match constrs with 
    | [] => None
    | h::t => 
        if (snd h =? constr)%string 
        then Some (fst h) 
        else lookup_type_constrs constr t 
    end.



Fixpoint lookup_type_sum (constr : string) (Σ : sum_types_constructors)
    : option (string * type) :=
    match Σ with 
    | [] => None 
    | h::Σ' => 
        match lookup_type_constrs constr (snd h)  with 
        | None => lookup_type_sum constr Σ'
        | Some t => Some (fst h, t) 
        end
    end.


(* Fixpoint expected_parameter 
  (constrs : list (type * string)) 
  (branches : list (string * expr)) : (list (string * expr * option type)) :=
  match branches with 
  | [] => []
  | h::branches' => 
    let name := fst h in 
    let e := snd h in 
    let t := lookup_type_constrs name constrs in 
    (name, e, t)::(expected_parameter constrs branches')
  end. *)

Inductive has_type : sum_types_constructors -> context -> expr -> type -> Prop := 
  (* Base λ-calculus *)
  | T_Var: 
      ∀ Γ Σ x t, 
      Γ ? x = Some t -> 
      has_type Σ Γ (E_Var x) t 
  | T_Fun: 
      ∀ Γ Σ x t1 e (t2 : type),
      has_type Σ (x |-> t1; Γ)  e  t2 -> 
      has_type Σ Γ  (E_Fun x t1 e)  (Type_Fun t1 t2) 

  | T_App: 
      ∀ Γ Σ e1 e2 t1 t2, 
      has_type Σ Γ  e2  t1 ->  
      has_type Σ Γ  e1  (Type_Fun t1 t2) -> 
      has_type Σ Γ  (E_App e1 e2)  t2 

  (* Booleans and conditions *)
  | T_True: 
      ∀ Γ Σ, 
      has_type Σ Γ  E_True  Type_Bool 
              
  | T_False: 
      ∀ Γ Σ, 
      has_type Σ Γ  E_False  Type_Bool 

  | T_If: 
      ∀ Γ Σ e1 e2 e3 t, 
      has_type Σ Γ  e1  Type_Bool ->  
      has_type Σ Γ  e2  t ->  
      has_type Σ Γ  e3  t ->  
      has_type Σ Γ  (E_If e1 e2 e3)  t  

  (* Let expressions *)
  | T_Let : 
      ∀ Γ Σ x e1 e2 t1 t2, 
      has_type Σ Γ  e1  t1 ->  
      has_type Σ (x |-> t1; Γ)  e2  t2 ->  
      has_type Σ Γ  (E_Let x e1 e2)  t2 

  (* Arithmetic *)
  | T_Num : 
      ∀ Γ Σ z, 
      has_type Σ Γ  (E_Num z)  Type_Num  

  | T_Minus : 
      ∀ Γ Σ e1 e2, 
      has_type Σ Γ e1 Type_Num -> 
      has_type Σ Γ e2 Type_Num -> 
      has_type Σ Γ (E_Minus e1 e2)  Type_Num  
    
  | T_Eq :
      ∀ Γ Σ e1 e2, 
      has_type Σ Γ e1 Type_Num -> 
      has_type Σ Γ e2 Type_Num -> 
      has_type Σ Γ (E_Eq e1 e2)  Type_Bool  

  (* Pairs *)
  | T_Pair :
      ∀ Γ Σ e₁ e₂ t₁ t₂, 
      has_type Σ Γ e₁ t₁ -> 
      has_type Σ Γ e₂ t₂ -> 
      has_type Σ Γ (E_Pair e₁ e₂)  (Type_Prod t₁ t₂)  
  | T_First :
      ∀ Γ Σ e t₁ t₂,
      has_type Σ Γ  e  (Type_Prod t₁ t₂) -> 
      has_type Σ Γ  (E_First e)  t₁ 
  | T_Second :
      ∀ Γ Σ e t₁ t₂,
      has_type Σ Γ  e  (Type_Prod t₁ t₂) -> 
      has_type Σ Γ  (E_Second e)  t₂ 

  (* Records *)
  | T_Record_Nil :
      ∀ Γ Σ, 
      has_type Σ Γ  (E_Record_Nil)  (Type_Record_Nil) 
  | T_Record_Cons :
      ∀ Γ Σ x e t_e e_tail t_tail, 
      has_type Σ Γ  e  t_e ->  

      has_type Σ Γ  e_tail  t_tail ->  
      record_type t_tail ->
      has_type Σ Γ  (E_Record_Cons x e e_tail)  (Type_Record_Cons x t_e t_tail)  
  | T_Record_Access :
      ∀ Γ Σ x e t_e t_acc, 
      has_type Σ Γ  e  t_e ->  
      lookup_type_record x t_e = Some t_acc ->
      has_type Σ Γ  (E_Record_Access e x)  t_acc 
  
  | T_Fix :
      ∀ Γ Σ e t, 
      has_type Σ Γ  e (Type_Fun t t) ->  
      has_type Σ Γ  (E_Fix e)  t 

  (* Sum types *)
  | T_Unit : ∀ Γ Σ, has_type Σ Γ E_Unit (Type_Unit)  
  | T_In_Left :
      ∀ Γ Σ t₁ t₂ e, 
      has_type Σ Γ  e  t₁ ->  
      has_type Σ Γ  (E_In_Left t₁ t₂ e)  (Type_Disjoint_Union t₁ t₂) 
  | T_In_Right :
      ∀ Γ Σ t₁ t₂ e, 
      has_type Σ Γ  e  t₂ ->  
      has_type Σ Γ  (E_In_Right t₁ t₂ e)  (Type_Disjoint_Union t₁ t₂) 
  | T_Match :
      ∀ Γ Σ t₁ t₂ tf e e_left e_right, 
      has_type Σ Γ e (Type_Disjoint_Union t₁ t₂) ->  
      has_type Σ Γ e_left  (Type_Fun t₁ tf) -> 
      has_type Σ Γ e_right  (Type_Fun t₂ tf) -> 
      has_type Σ Γ (E_Match e e_left e_right) tf 

  | T_Sum_Constr: 
      ∀ Γ Σ e constr name t,
      lookup_type_sum constr Σ = Some (name, t) -> 
      has_type Σ Γ e t ->
      has_type Σ Γ (E_Sum_Constr constr e) (Type_Sum name)

  | T_Sum_Match : 
    ∀ Σ Γ t e name_sum branches, 
    has_type Σ Γ e (Type_Sum name_sum) -> 
    has_type_lsexpr name_sum Σ Γ branches t ->
    has_type Σ Γ (E_Sum_Match e branches) t

  | T_Exception :
      ∀ Σ Γ e t,
      has_type Σ Γ (E_Exception e) t
with has_type_lsexpr : string -> sum_types_constructors -> context -> lsexpr -> type -> Prop :=
    | T_LSExpr_Nil :
        ∀ 
          (name_sum constr : string) 
          (Σ : sum_types_constructors) 
          (Γ : context) 
          (t t': type), 

        lookup_type_sum constr Σ = Some (name_sum, t') -> 
        has_type_lsexpr name_sum Σ Γ LSE_Nil t
        
    | T_LSExpr_Cons :
        ∀ name_sum Σ Γ tail constr e t_arg t, 
        has_type_lsexpr name_sum Σ Γ tail t -> 
        lookup_type_sum constr Σ = Some (name_sum, t_arg) -> 
        has_type Σ Γ e {{ t_arg -> t }} -> 
        has_type_lsexpr name_sum Σ Γ (LSE_Cons constr e tail)  t
.

Hint Constructors has_type : local_hints.
Hint Constructors has_type_lsexpr : local_hints.





Lemma weakening : 
  ∀ e Γ Γ' Σ t ,
        Maps.includedin Γ Γ' ->
        has_type Σ Γ e t ->
        has_type Σ Γ' e t.
Proof with eauto with local_hints.
  pose (
    P (e : expr) :=
      ∀ Γ Γ' Σ t ,
        Maps.includedin Γ Γ' ->
        has_type Σ Γ e t ->
        has_type Σ Γ' e t
  ).
  pose (
    P0 (branches : lsexpr) :=
      ∀ Γ Γ' Σ t name_sum,
        Maps.includedin Γ Γ' ->
        has_type_lsexpr name_sum Σ Γ branches t ->
        has_type_lsexpr name_sum Σ Γ' branches t
  ).
  
  intro e.
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0; intros; try (try inversion H0; try inversion H1; try inversion H2; try inversion H3; subst; eauto with local_hints; fail).
  - inversion H1; subst. eapply T_Fun.
    apply H with (Γ := (x |-> t; Γ))... 
    apply Maps.includedin_update...
  - inversion H2; subst. eapply T_Let...   
    apply H0 with (Γ := (x |-> t1; Γ))... 
    apply Maps.includedin_update...
Qed.

Hint Resolve weakening : local_hints.



Lemma weakening_empty : ∀ Γ Σ e t, 
  has_type Σ empty e t -> 
  has_type Σ Γ e t. 
Proof.
  intros. apply weakening with empty.
  - intros x v contra. discriminate contra.
  - assumption.
Qed.


Lemma weakening_eq :
  ∀ Γ₁ Γ₂ Σ e t, 
  Maps.eq Γ₁ Γ₂ -> 
  has_type Σ Γ₁  e  t -> 
  has_type Σ Γ₂ e t. 
Proof.
  intros.
  apply weakening with Γ₁.
  - apply Maps.includedin_eq. assumption.
  - assumption.
Qed. 

Hint Resolve weakening_empty : local_hints.
Hint Resolve weakening_eq : local_hints.




