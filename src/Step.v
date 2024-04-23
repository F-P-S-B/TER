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

Reserved Notation "x --> y" (at level 70, no associativity).
Reserved Notation "x -->ₗ y" (at level 70, no associativity).
Inductive step : expr -> expr -> Prop := 
  | ST_App_Fun : 
        ∀ (x : string) (t : type) (e e' v : expr),
        value v -> 
        substitution v x e e' ->
        <{(fun x : t => e) v}> --> e'

  | ST_App_Left : 
      ∀ (e₁ e₁' e₂ : expr),
      e₁ --> e₁' ->
      <{e₁ e₂}> --> <{e₁' e₂}>

  | ST_App_Right : 
      ∀ (v e e' : expr),
      value v ->
      e --> e' ->
      <{v e}> --> <{v e'}>

  | ST_If_True : 
      ∀ (e₁ e₂ : expr),
      <{if true then e₁ else e₂}> --> e₁
      
  | ST_If_False : 
      ∀ (e₁ e₂ : expr),
      <{if false then e₁ else e₂}> --> e₂

  | ST_If : 
      ∀ (e₁ e₁' e₂ e₃ : expr),
      e₁ --> e₁' ->
      <{if e₁ then e₂ else e₃}> --> <{if e₁' then e₂ else e₃}>


  | ST_Let_Left : 
      ∀ (x : string) (e₁ e₁' e₂ : expr),
      e₁ --> e₁' ->
      <{let x = e₁ in e₂}>  -->  <{let x = e₁' in e₂}> 

  | ST_Let_Right : 
      ∀ (x : string) (v e e' : expr),
      value v ->
      substitution v x e e' ->
      <{ let x = v in e }> --> e'

  
  | ST_Minus_Left :  
      ∀ (e₁ e₁' e₂ : expr),
      e₁ --> e₁' ->
      <{ e₁ - e₂ }> --> <{ e₁' - e₂ }>

  | ST_Minus_Right :  
      ∀ (v e e' : expr),
      value v ->
      e --> e' ->
      <{ v - e }> --> <{ v - e'}>

  | ST_Minus_Num : 
      ∀ (z₁ z₂ : Z),
      <{ z₁ - z₂ }> --> <{ `z₁ - z₂` }>
  

  | ST_Eq_Left :  
      ∀ (e₁ e₁' e₂ : expr),
      e₁ --> e₁' ->
      <{ e₁ == e₂ }> --> <{ e₁' == e₂ }>

  | ST_Eq_Right :  
      ∀ (v e e' : expr),
      value v ->
      e --> e' ->
      <{ v == e }> --> <{ v == e' }>

  | ST_Eq_Num_Eq : 
      ∀ (z : Z),
      <{ z == z }> --> <{ true }>

  | ST_Eq_Num_Neq : 
      ∀ (z₁ z₂ : Z),
      z₁ <> z₂ ->
      <{ z₁ == z₂ }> --> <{ false }>


  | ST_Pair_Left :  
      ∀ (e₁ e₁' e₂ : expr),
      e₁ --> e₁' ->
      <{ (e₁, e₂) }> --> <{ (e₁', e₂) }> 

  | ST_Pair_Right :  
      ∀ (v e e' : expr),
      value v ->
      e --> e' ->
      <{ (v, e) }> --> <{ (v, e') }> 

  | ST_First :  
      ∀ (e e' : expr),
      e --> e' ->
      <{first e}> --> <{first e'}>

  | ST_First_Pair :  
      ∀ (v₁ v₂ : expr),
      value v₁ -> 
      value v₂ ->
      <{first (v₁, v₂)}> --> v₁

  | ST_Second :  
      ∀ (e e' : expr),
      e --> e' ->
      <{second e}> --> <{second e'}>

  | ST_Second_Pair :  
      ∀ (v₁ v₂ : expr),
      value v₁ -> 
      value v₂ ->
      <{second (v₁, v₂)}> --> v₂

  
  | ST_Records : 
      ∀ (rec rec': lsexpr),
      rec -->ₗ rec' -> 
      <{ { rec } }> --> <{ { rec' } }>

  | ST_Access : 
      ∀ (x : string) (e e' : expr),
      e --> e' -> 
      <{ e::x }> --> <{ e'::x }>

  | ST_Access_Value : 
      ∀ x e e',
      value_lsexpr e -> 
      lookup_lsexpr x e = Some e' ->
      <{ { e }::x }> --> e'

  
  | ST_Fix :
      ∀ (e e': expr),
      e --> e' ->
      <{ fix e }> --> <{ fix e' }>
  
  | ST_Fix_Fun :
      ∀ (x : string) (t : type) (e e': expr),
      substitution <{ fix (fun x : t => e)}> x e e' ->
      <{ fix (fun x : t => e) }> --> e'
  

  | ST_In_Left :
      ∀ (t₁ t₂ : type) (e e' : expr), 
      e --> e' -> 
      <{ inl <t₁ | t₂> e }> --> <{ inl <t₁ | t₂> e' }>

  | ST_In_Right :
      ∀ (t₁ t₂ : type) (e e' : expr), 
      e --> e' -> 
      <{ inr <t₁ | t₂> e }> --> <{ inr <t₁ | t₂> e' }>
  
  | ST_Match_Main :
      ∀ (e e' eₗ eᵣ : expr),
      e --> e' ->
      <{ match e with | inl => eₗ | inr =>  eᵣ end }> --> 
      <{ match e' with | inl => eₗ | inr =>  eᵣ end }>

  | ST_Match_Left :
      ∀ (v eₗ eₗ' eᵣ : expr),
      value v ->
      eₗ --> eₗ' -> 
      <{ match v with | inl => eₗ | inr =>  eᵣ end }> --> 
      <{ match v with | inl => eₗ' | inr =>  eᵣ end }>

  | ST_Match_Right :
      ∀ (v vₗ eᵣ eᵣ' : expr),
      value v ->
      value vₗ ->
      eᵣ --> eᵣ' -> 
      <{ match v with | inl => vₗ | inr =>  eᵣ end }> --> 
      <{ match v with | inl => vₗ | inr =>  eᵣ' end }>

  | ST_Match_Left_App :
      ∀ (t₁ t₂ : type) (v vₗ vᵣ : expr),
      value v ->
      value vₗ ->
      value vᵣ ->
      <{ match inl <t₁ | t₂> v with | inl => vₗ | inr =>  vᵣ end }> --> 
      <{vₗ v}>

  | ST_Match_Right_App :
    ∀ (t₁ t₂ : type) (v vₗ vᵣ : expr),
      value v ->
      value vₗ ->
      value vᵣ ->
      <{ match inr <t₁ | t₂> v with | inl => vₗ | inr =>  vᵣ end }> --> 
      <{vᵣ v}>
  
  | ST_Sum_Constr :
      ∀ (constr : string) (e e' : expr),
      e --> e' -> 
      <{constr[e]}> --> <{constr[e']}>

  | ST_Sum_Match_Main : 
      ∀ (e e' default : expr) (branches : lsexpr), 
      e --> e' -> 
      <{match_sum e  with branches : default end_sum }> --> 
      <{match_sum e' with branches : default end_sum }>

  | ST_Sum_Match :
      ∀ (v default : expr) (branches branches' : lsexpr), 
      value v -> 
      branches -->ₗ branches' ->
      <{match_sum v with branches  : default end_sum }> --> 
      <{match_sum v with branches' : default end_sum }>
  
  | ST_Sum_Match_Default :
      ∀ (v default default' : expr) (branches : lsexpr), 
      value v -> 
      value_lsexpr branches ->
      default --> default' ->
      <{match_sum v with branches : default  end_sum }> --> 
      <{match_sum v with branches : default' end_sum }>

  | ST_Sum_Match_Apply :
      ∀ (constr : string) (v b default: expr) (branches : lsexpr), 
      value v -> 
      value_lsexpr branches ->
      value default -> 
      lookup_lsexpr constr branches = Some b ->
      <{match_sum constr[v] with branches : default end_sum }> 
      --> <{b v}>
  | ST_Sum_Match_Apply_Not_Found :
      ∀ (constr : string) (v default: expr) (branches : lsexpr), 
      value v -> 
      value_lsexpr branches ->
      value default -> 
      lookup_lsexpr constr branches = None ->
      <{match_sum constr[v] with branches : default end_sum }> 
      --> default
where
  "x --> y" := (step x y)
with 
  step_lsexpr : lsexpr -> lsexpr -> Prop := 
    | ST_LSExpr_Cons :
        ∀ (x : string) (e e' : expr) (tail : lsexpr),
        e --> e' -> 
        <{ x := e ; tail}> -->ₗ <{ x := e' ; tail}>

    | ST_LSExpr_Tail :
        ∀ (x : string) (v : expr) (tail tail' : lsexpr),
        value v -> 
        tail -->ₗ tail' ->
        <{ x := v ; tail}> -->ₗ <{ x := v ; tail'}>
where 
    "x -->ₗ y" := (step_lsexpr x y)
.


Hint Constructors step : local_hints.
Hint Constructors step_lsexpr : local_hints.

Local Lemma not_value: 
  ∀ e e',
  value e -> 
  ¬ e --> e'.
Proof with eauto with local_hints.
  intro e.
  pose (
    P (e : expr) :=
      ∀ e',
      value e -> 
      ¬ e --> e'
  ).
  pose (
    P0 (branches : lsexpr) :=
      ∀ branches',
      value_lsexpr branches -> 
      ¬ branches -->ₗ branches'
  ).
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0;
  clear e P P0;
  try (
    intros * IH * H_val H_contra;
    inversion H_val;
    inversion H_contra; subst;
    try (eapply IH; eauto with local_hints; fail);
    fail
  );
   intros; intro H_contra;
  repeat (match goal with 
  | [ H_contra : _ --> _ |- _] => solve [inversion H_contra]
  | [ H_contra : _ -->ₗ _ |- _] => solve [inversion H_contra]
  | [ H_val : value _ , 
      H_contra : _ --> _,
      IH1 : ∀ _, _ -> ¬ _,
      IH2 : ∀ _, _ -> ¬ _,
      IH3 : ∀ _, _ -> ¬ _
      |- _ ] => 
        inversion H_val;
        inversion H_contra; subst;
        try (eapply IH1; eauto with local_hints; fail);
        try (eapply IH2; eauto with local_hints; fail);
        try (eapply IH3; eauto with local_hints; fail)
  | [ H_val : value _ , 
      H_contra : _ --> _,
      IH1 : ∀ _, _ -> ¬ _,
      IH2 : ∀ _, _ -> ¬ _
      |- _ ] => 
        inversion H_val;
        inversion H_contra; subst;
        try (eapply IH1; eauto with local_hints; fail);
        try (eapply IH2; eauto with local_hints; fail);
        fail
  | [ H_val : value _ , 
      H_contra : _ --> _, 
      IH1 : ∀ _, _ -> ¬ _
      |- _ ] => 
        inversion H_val;
        inversion H_contra; subst;
        try (eapply IH1; eauto with local_hints);
        fail
  | [ H_val : value_lsexpr _ , 
      H_contra : _ -->ₗ _, 
      IH1 : ∀ _, _ -> ¬ _
      |- _ ] => 
        inversion H_val;
        inversion H_contra; subst;
        try (eapply IH1; eauto with local_hints; fail)
  end).
Qed.
Hint Resolve not_value : local_hints.

Local Lemma not_value_lsexpr :
  ∀ branches branches', 
  value_lsexpr branches -> 
  ¬ (branches -->ₗ branches').
Proof with eauto with local_hints.
  intros.
  generalize dependent branches'.
  induction H; intros branches' H_contra.
  - inversion H_contra.
  - inversion H_contra; subst.
    + eapply not_value...
    + eapply IHvalue_lsexpr...
Qed.

Local Ltac not_value_contra := 
    match goal with 
      | [ H_val : value ?thise, 
          H_st : ?thise --> _ 
          |- _ ] => 
          exfalso; eapply not_value with (e:=thise); eauto with local_hints
      | [ H_val : value_lsexpr ?thisb, 
          H_st : ?thisb -->ₗ _ 
          |- _ ] => 
          exfalso; eapply not_value_lsexpr with (branches:=thisb); eauto with local_hints
      end.

Local Ltac det_subst :=
  match goal with 
      | [ _: substitution _ _ _ _,
          _: substitution _ _ _ _
          |- _ = _] => 
            eapply Subst.deterministic; eauto with local_hints
  end.

Local Ltac by_constr := f_equal; eauto with local_hints; fail.

Local Ltac impossible_red := 
  match goal with
      | [ H_st :  _ --> _
          |- _ ] => inversion H_st; fail
      end.

Local Ltac handle_lookup :=
  repeat (match goal with 
    | [ H : lookup_lsexpr _ _ = Some _ 
        |- _] =>
          rewrite H in *
    | [ H : Some _ = Some _
        |- _ ] =>  
        inversion H;
        subst; eauto with local_hints
    | [ H : Some _ = None |- _] => inversion H
    | [ H : None = Some _ |- _] => inversion H
    end); fail.

Ltac my_auto := 
  try by_constr; 
  try det_subst;
  try impossible_red; 
  try not_value_contra;
  try handle_lookup
.

Local Theorem deterministic :
    ∀ e e'₁ e'₂, 
    e --> e'₁ ->
    e --> e'₂ ->
    e'₁ = e'₂.
Proof with eauto with local_hints.
  intro e.
  pose (
    P (e : expr) :=
      ∀ e'₁ e'₂, 
      e --> e'₁ ->
      e --> e'₂ ->
      e'₁ = e'₂
  ).
  pose (
    P0 (branches : lsexpr) :=
      ∀ branches1' branches2',
      branches -->ₗ branches1' ->
      branches -->ₗ branches2' ->
      branches1' = branches2' 
  ).
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0;
  clear e P P0; 
  try (
    intros;
  match goal with 
  | [ H_st1 : _ --> _ ,
      H_st2 : _ --> _ 
      |- _] => inversion H_st1; inversion H_st2; fail
  | [ H_st1 : _ -->ₗ _ ,
      H_st2 : _ -->ₗ _ 
      |- _] => inversion H_st1; inversion H_st2; fail
  | [ H_st1 : _ --> _ ,
      H_st2 : _ --> _ ,
      IH : ∀ _ _, _ -> _ -> _
      |- _] =>
    inversion H_st1; subst; inversion H_st2; subst; my_auto; contradiction; fail
  end);
  try (
    intros * IH1 * IH2 * IH3 * H_st1 H_st2;
    inversion H_st1; subst;
    inversion H_st2; subst;
    my_auto;
    fail
  );
  try (
    intros * IH1 * IH2 * H_st1 H_st2;
    inversion H_st1; subst;
    inversion H_st2; subst;
    my_auto;
    contradiction;
    fail
  ).
  - intros * IH * H_st1 H_st2.
    inversion H_st1; subst;
    inversion H_st2; subst;
    try by_constr;
    match goal with 
    | [ H : <{ (_, _) }>  --> _ |- _] => inversion H; not_value_contra
    end.
  - intros * IH * H_st1 H_st2.
    inversion H_st1; subst;
    inversion H_st2; subst;
    try by_constr;
    match goal with 
    | [ H : <{ (_, _) }>  --> _ |- _] => inversion H; not_value_contra
    end.
  - intros * IH * H_st1 H_st2.
    inversion H_st1;
    inversion H_st2; subst;
    match goal with 
    | [ H_st : <{ { _ } }> --> _,
        H_val : value_lsexpr _
        |- _] => 
        inversion H_st;
        not_value_contra
    | [ H_eq : <{ { _ } }> = <{ { _ } }>
        |- _] =>
          inversion H_eq;
          subst
    | _ => idtac
    end;
    my_auto.
  - intros * IH1 * IH2 * IH3 * H_st1 H_st2.
    inversion H_st1; subst;
    inversion H_st2; subst; my_auto;
    match goal with 
    | [ H : <{ inl < _ | _ > _ }> --> _ 
        |- _] => 
          inversion H
    | [ H : <{ inr < _ | _ > _ }> --> _ 
        |- _] => 
          inversion H
    end;
    not_value_contra.
  - intros * IH1 * IH2 * IH3 * H_st1 H_st2.
    inversion H_st1; subst;
    inversion H_st2; subst; 
    my_auto;
    match goal with 
    | [ H : E_Sum_Constr _ _ --> _ 
        |- _] => 
          inversion H; not_value_contra
    end.
Qed.
