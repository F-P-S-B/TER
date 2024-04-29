From Coq Require Import Unicode.Utf8.
Require Import String.
Require Import List.
Import ListNotations.
Local Open Scope Z_scope.
Require Import ZArith.

Require Maps.
Import Maps.Notations.
Require Import Hints.
Require Import Syntax.

Definition context : Set := @Maps.map type.
Definition empty : context := @Maps.empty type.
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


Reserved Notation "Σ '/'  Γ  '|-'  e  ':'  t" (
    at level 0,
    e custom expr
). 

Reserved Notation "Σ '/'  Γ  '|-ᵣ'  e  ':'  t" (
    at level 0,
    e custom expr
). 


Reserved Notation "Σ '/' Γ  |-ₛ name_sum ~> e : t" (
    at level 0,
    e custom expr
). 


Inductive has_type : sum_types_constructors -> context -> expr -> type -> Prop := 
  (* Base λ-calculus *)
  | T_Var : 
      ∀ (Γ : context) (Σ : sum_types_constructors) (x : string) (t : type), 
      Γ ? x = Some t -> 
      Σ / Γ |- #x : t

  | T_Fun : 
      ∀ (Σ : sum_types_constructors) (Γ : context) 
        (x : string) (e : expr) (t₁ t₂ : type),
      Σ / (x |-> t₁ ; Γ) |- e : t₂ -> 
      Σ / Γ |- fun x : t₁ => e : {{ t₁ -> t₂ }}
  
  | T_App :
      ∀ (Σ : sum_types_constructors) (Γ : context)  
        (e₁ e₂ : expr) (t₁ t₂ : type), 
      Σ / Γ |- e₂ : t₁ ->  
      Σ / Γ |- e₁ : {{ t₁ -> t₂ }} -> 
      Σ / Γ |- <{ e₁ e₂ }> : t₂ 

  (* Booleans and conditions *)
  | T_True: 
      ∀ (Σ : sum_types_constructors) (Γ : context), 
      Σ / Γ |- <{true}> : {{ Bool }} 
              
  | T_False: 
      ∀ (Σ : sum_types_constructors) (Γ : context), 
      Σ / Γ |- <{false}> : {{ Bool }} 

  | T_If: 
      ∀ Γ Σ e₁ e₂ e₃ t, 
      Σ / Γ |- e₁ : {{ Bool }} ->  
      Σ / Γ |- e₂ : t ->  
      Σ / Γ |- e₃ : t ->  
      Σ / Γ |- <{ if e₁ then e₂ else e₃ }> : t 

  (* Let expressions *)
  | T_Let : 
      ∀ (Σ : sum_types_constructors) (Γ : context) 
        (x : string) (e₁ e₂ : expr) (t₁ t₂ : type),
      Σ / Γ |- e₁ : t₁ ->  
      Σ / (x |-> t₁; Γ) |- e₂ : t₂ ->  
      Σ / Γ |- <{let x = e₁ in e₂}> : t₂ 

  (* Arithmetic *)
  | T_Num : 
      ∀ (Σ : sum_types_constructors) (Γ : context) (z : Z), 
      Σ / Γ |- <{ z }> : {{ Int }}  

  | T_Minus : 
      ∀ (Σ : sum_types_constructors) (Γ : context) (e₁ e₂ : expr), 
      Σ / Γ |- e₁ : {{ Int }} -> 
      Σ / Γ |- e₂ : {{ Int }} -> 
      Σ / Γ |- e₁ - e₂ : {{ Int }}  
    
  | T_Eq :
      ∀ (Σ : sum_types_constructors) (Γ : context) (e₁ e₂ : expr), 
      Σ / Γ |- e₁ : {{ Int }} -> 
      Σ / Γ |- e₂ : {{ Int }} -> 
      Σ / Γ |- e₁ == e₂ : {{ Bool }}  

  (* Pairs *)
  | T_Pair :
      ∀ (Σ : sum_types_constructors) (Γ : context) 
        (e₁ e₂ : expr) (t₁ t₂ : type),
      Σ / Γ |- e₁ : t₁ -> 
      Σ / Γ |- e₂ : t₂ -> 
      Σ / Γ |- <{ ( e₁,  e₂ ) }> : {{t₁ * t₂}}  
  | T_First :
      ∀ (Σ : sum_types_constructors) (Γ : context) 
        (e : expr) (t₁ t₂ : type),
      Σ / Γ |- e : {{ t₁ * t₂ }} -> 
      Σ / Γ |- first e : t₁ 
  | T_Second :
      ∀ (Σ : sum_types_constructors) (Γ : context) 
        (e : expr) (t₁ t₂ : type),
      Σ / Γ |- e : {{ t₁ * t₂ }} -> 
      Σ / Γ |- second e : t₂ 

  (* Records *)
  
  | T_Recordt :
      ∀ (Σ : sum_types_constructors) (Γ : context) (rec : lsexpr) (tᵣ : lstype),
      Σ / Γ |-ᵣ rec : tᵣ -> 
      Σ / Γ |- { rec } : {{ { tᵣ } }}  

  | T_Record_Access :
      ∀ (Σ : sum_types_constructors) (Γ : context) 
        (e : expr) (tᵣ : lstype) (x : string) (t : type),
      Σ / Γ |- e : {{ { tᵣ } }} -> 
      lookup_lstype x tᵣ = Some t ->
      Σ / Γ |- e::x : t

  (* Fixpoints *)
  | T_Fix :
      ∀ (Σ : sum_types_constructors) (Γ : context) (e : expr) (t : type), 
      Σ / Γ |- e : {{ t -> t }} ->  
      Σ / Γ |- fix e : t 

  (* Sum types *)
  | T_Unit : 
      ∀ (Σ : sum_types_constructors) (Γ : context), 
      Σ / Γ |- unit : {{ Unit }}
  | T_In_Left :
      ∀ (Σ : sum_types_constructors) (Γ : context) (e: expr) (t₁ t₂ : type), 
      Σ / Γ |-  e : t₁ ->  
      Σ / Γ |-  inl <t₁ | t₂> e :  {{ t₁ + t₂ }} 
  | T_In_Right :
      ∀ (Σ : sum_types_constructors) (Γ : context) (e: expr) (t₁ t₂ : type), 
      Σ / Γ |-  e : t₂ ->  
      Σ / Γ |-  inr <t₁ | t₂> e :  {{ t₁ + t₂ }}
  | T_Match :
      ∀ (Σ : sum_types_constructors) (Γ : context) 
        (t₁ t₂ tₑ : type) (e eₗ eᵣ : expr), 
      Σ / Γ |- e : {{ t₁ + t₂ }} ->  
      Σ / Γ |- eₗ : {{ t₁ -> tₑ }} -> 
      Σ / Γ |- eᵣ : {{ t₂ -> tₑ }} -> 
      Σ / Γ |- match e with | inl => eₗ | inr => eᵣ end : tₑ
  
  | T_Sum_Constr: 
      ∀ (Σ : sum_types_constructors) (Γ : context) 
        (e : expr) (constr name : string) (t : type),
      lookup_type_sum constr Σ = Some (name, t) -> 
      Σ / Γ |- e : t ->
      Σ / Γ |- constr[e] : (Type_Sum name)

  | T_Sum_Match : 
      ∀ (Σ : sum_types_constructors) (Γ : context)
        (t : type) (e default: expr) 
        (name_sum : string) (branches : lsexpr), 
      Σ / Γ |- e : (Type_Sum name_sum) -> 
      Σ / Γ |- default : t -> 
      Σ / Γ |-ₛ name_sum ~> branches : t ->
      Σ / Γ |- <{match_sum e with branches : default end_sum}> : t
  where 
    "Σ '/' Γ |- e : t" := (has_type Σ Γ e t)
  with 
    has_type_record : sum_types_constructors -> context -> lsexpr -> lstype -> Prop :=
    | TRec_Nil :
        ∀ (Σ : sum_types_constructors) (Γ : context),
        Σ / Γ |-ᵣ nil : {{ Nil }}
    | TRec_Cons :
        ∀ (Σ : sum_types_constructors) (Γ : context)
          (x: string) (e : expr) (rec : lsexpr) (t : type) (tᵣ : lstype) ,
        Σ / Γ |-ᵣ rec : tᵣ -> 
        Σ / Γ |- e : t -> 
        Σ / Γ |-ᵣ x := e ; rec : {{ x : t ; tᵣ }}
  where 
    "Σ '/' Γ |-ᵣ e : t" := (has_type_record Σ Γ e t)

  with 
    has_type_branches : string -> sum_types_constructors -> context -> lsexpr -> type -> Prop :=
    | TB_Nil :
        ∀ (name_sum : string) 
          (Σ : sum_types_constructors) 
          (Γ : context) 
          (t t': type), 
        Σ / Γ |-ₛ name_sum ~> nil : t

    | TB_Cons :
        ∀ (name_sum constr : string) 
          (Σ : sum_types_constructors) 
          (Γ : context) 
          (e : expr)
          (tail : lsexpr)
          (t tₐ: type), 
        Σ / Γ |-ₛ name_sum ~> tail : t -> 
        lookup_type_sum constr Σ = Some (name_sum, tₐ) ->
        Σ / Γ |- e : {{ tₐ -> t }} -> 
        Σ / Γ |-ₛ name_sum ~> constr := e ; tail : t 


  where 
    "Σ '/' Γ  |-ₛ name_sum ~> e : t" := (has_type_branches name_sum Σ Γ e t)
.

Hint Constructors has_type : local_hints.
Hint Constructors has_type_record : local_hints.
Hint Constructors has_type_branches : local_hints.



Theorem weakening : 
  ∀ e Σ Γ Γ' t ,
        Maps.includedin Γ Γ' ->
        Σ / Γ |- e : t ->
        Σ / Γ'|- e : t.
Proof with eauto with local_hints.
assert (MapsIncluded: 
    ∀ Γ Γ' x (t : type), 
    Maps.includedin Γ Γ' -> Maps.includedin (x |-> t; Γ) (x |-> t; Γ')
) by apply Maps.includedin_update.
  pose (
    P (e : expr) :=
      ∀ Σ Γ Γ' t ,
        Maps.includedin Γ Γ' ->
        Σ / Γ |- e : t ->
        Σ / Γ'|- e : t
  ).
  pose (
    P0 (branches : lsexpr) :=
      ∀ Σ Γ Γ',
        Maps.includedin Γ Γ' ->
        (
          ∀ name_sum t,
          Σ / Γ |-ₛ name_sum ~> branches : t ->
          Σ / Γ' |-ₛ name_sum ~> branches : t 
        ) /\ 
        (
          ∀ t,
          Σ / Γ |-ᵣ branches : t ->
          Σ / Γ' |-ᵣ branches : t 
        )
  ).
  
  intro e.
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0; clear e P P0; intros;
  match goal with 
  | [ |- _ /\ _ ] => split; intros
  | _ => idtac
  end;
  match goal with 
  | [ H_type : (_  / _ |- _ : _) |- _] =>
      inversion H_type; subst; eauto with local_hints
  | [ H_type : (_  / _ |-ₛ _ ~> _ : _) |- _] =>
      inversion H_type; subst; eauto with local_hints
  | [ H_type : (_  / _ |-ᵣ _ : _) |- _] =>
      inversion H_type; subst; eauto with local_hints
  | _ => idtac
  end;
  match goal with 
  | [ IH : (∀ _ _ _, _ -> _ /\ _),
      H_included : Maps.includedin _ _
       |- _ ] => edestruct IH; eauto with local_hints
  | _ => idtac
  end.
Qed.


Hint Resolve weakening : local_hints.



Corollary weakening_empty : ∀ Γ Σ e t, 
  has_type Σ empty e t -> 
  has_type Σ Γ e t. 
Proof.
  intros. apply weakening with empty.
  - intros x v contra. discriminate contra.
  - assumption.
Qed.


Corollary weakening_eq :
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


Lemma lookup_has_type :
  ∀ Σ Γ x lse e lst t,
  Σ / Γ |-ᵣ lse : lst -> 
  lookup_lsexpr x lse = Some e ->
  lookup_lstype x lst = Some t -> 
  Σ / Γ |- e : t.
Proof with eauto with local_hints.
  intros * H_type_ls.
  induction H_type_ls.
  - intros * H_lookup_e H_lookup_t. inversion H_lookup_e.
  - intros * H_lookup_e H_lookup_t.
    simpl in *.
    destruct (String.eqb_spec x0 x); subst...
    inversion H_lookup_e.
    inversion H_lookup_t; subst...
Qed.


Lemma lookup_branches_type_fun :
  ∀ Σ Γ name_sum constr branches t b tₐ,
  (Σ) / Γ |-ₛ name_sum ~> branches : (t) -> 
  lookup_lsexpr constr branches = Some b ->
  lookup_type_sum constr Σ = Some (name_sum, tₐ) ->
  Σ / Γ |- b : {{ tₐ -> t }}.
Proof with eauto with local_hints.
  intros * H_type_branches H_lookup_branches H_lookup_Σ.
  induction H_type_branches.
  - inversion H_lookup_branches.
  - simpl in *.
    destruct (String.eqb_spec constr0 constr); subst...
    inversion H_lookup_branches; subst.
    rewrite H in H_lookup_Σ.
    inversion H_lookup_Σ; subst...
Qed.