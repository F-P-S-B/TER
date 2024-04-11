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
      E_Sum_Constr constr e --> E_Sum_Constr constr e'

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
      <{match_sum `E_Sum_Constr constr v` with branches : default end_sum }> 
      --> <{b v}>
  | ST_Sum_Match_Apply_Not_Found :
      ∀ (constr : string) (v default: expr) (branches : lsexpr), 
      value v -> 
      value_lsexpr branches ->
      value default -> 
      lookup_lsexpr constr branches = None ->
      <{match_sum `E_Sum_Constr constr v` with branches : default end_sum }> 
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

Check ∀ (z₁ z₂ : Z),
      <{ z₁ - z₂ }> --> <{ `z₁ - z₂` }>.

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
  clear P P0;
  try (
    intros * IH1 * IH2 * IH3 * H_val H_contra;
    inversion H_val;
    inversion H_contra; subst;
    try (eapply IH1; eauto with local_hints; fail);
    try (eapply IH2; eauto with local_hints; fail);
    try (eapply IH3; eauto with local_hints; fail);
    fail
  );
  try (
    intros * IH1 * IH2 * H_val H_contra;
    inversion H_val;
    inversion H_contra; subst;
    try (eapply IH1; eauto with local_hints; fail);
    try (eapply IH2; eauto with local_hints; fail);
    fail
  );
  try (
    intros * IH * H_val H_contra;
    inversion H_val;
    inversion H_contra; subst;
    try (eapply IH; eauto with local_hints; fail);
    fail
  );
  try (
    intros * H_val H_contra;
    inversion H_contra;
    fail
  ).
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
  clear P P0;
  try (
    intros * H_st1 H_st2;
    inversion H_st1;
    inversion H_st2;
    fail
  );
  try (
    intros * IH * H_st1 H_st2;
    inversion H_st1;
    inversion H_st2;
    try (f_equal; eauto with local_hints; fail);
    try (exfalso; eapply not_value; eauto with local_hints; fail);
    try (inversion H2; fail);
    try (inversion H3; fail);
    fail
  );
  try (
    intros * IH1 * IH2 * H_st1 H_st2;
    inversion H_st1; subst;
    inversion H_st2; subst;
    try (eapply Subst.deterministic; eauto with local_hints; fail);
    try (f_equal; eauto with local_hints; fail);
    try (exfalso; eapply not_value; eauto with local_hints; fail);
    fail
  ).
  - intros * IH1 * IH2 * H_st1 H_st2.
    inversion H_st1; subst.
    + inversion H_st2; subst...
      * eapply Subst.deterministic...
      * inversion H4.
      * exfalso; eapply not_value with (e:=e2)...
    + inversion H_st1; subst; 
      try (
        inversion H_st2; subst;try (simpl in *; eauto with local_hints; fail); 
        try (inversion H0; fail);
        f_equal; eauto with local_hints;
        try (exfalso; eapply not_value; eauto with local_hints; fail);
        fail
      ).
      inversion H2.
    + inversion H_st2; subst;
      try (exfalso; eapply not_value; eauto with local_hints; fail).
      f_equal...
  - intros * IH1 * IH2 * IH3 * H_st1 H_st2.
    inversion H_st1; subst; 
    try (
      inversion H_st2; subst; eauto with local_hints; 
      try (inversion H3; fail); 
      f_equal; eauto with local_hints; fail
    ).
  - intros * IH1 * IH2 * H_st1 H_st2.
    inversion H_st1; subst.
    + inversion H_st2; subst.
      * f_equal...
      * exfalso; eapply not_value...
      * inversion H2.
    + inversion H_st2; subst.
      * exfalso; eapply not_value...
      * f_equal...
      * inversion H3.
    + inversion H_st2; subst...
      * inversion H2.
      * inversion H3.
  - intros * IH1 * IH2 * H_st1 H_st2.
    inversion H_st1; subst.
    + inversion H_st2; subst.
      * f_equal...
      * exfalso; eapply not_value...
      * inversion H2.
      * inversion H2.
    + inversion H_st2; subst.
      * exfalso; eapply not_value...
      * f_equal...
      * inversion H3.
      * inversion H3.
    + inversion H_st2; subst...
      * inversion H2.
      * inversion H3.
      * contradiction.
    + inversion H_st2; subst...
      * inversion H3.
      * inversion H4.
      * contradiction.
  - intros * IH * H_st1 H_st2.
    inversion H_st1; subst;
    inversion H_st2; subst;
    try (f_equal; eauto with local_hints).
    + inversion H0; subst.
      * exfalso; eapply not_value with (e:=e'₂)...
      * exfalso; eapply not_value with (e:=v₂)...
    + inversion H2; subst.
      * exfalso; eapply not_value with (e:=e'₁)...
      * exfalso; eapply not_value with (e:=v₂)... 
  - intros * IH * H_st1 H_st2.
    inversion H_st1; subst;
    inversion H_st2; subst;
    try (f_equal; eauto with local_hints).
    + inversion H0; subst.
      * exfalso; eapply not_value with (e:=v₁)...
      * exfalso; eapply not_value with (e:=e'₂)...
    + inversion H2; subst.
      * exfalso; eapply not_value with (e:=v₁)...
      * exfalso; eapply not_value with (e:=e'₁)... 
  - intros * IH * H_st1 H_st2.
    inversion H_st1;
    inversion H_st2; subst.
    + f_equal... 
    + exfalso; eapply not_value with (e:=<{ { e2 } }>)...
    + exfalso; eapply not_value with (e:=<{ { e1 } }>)... 
    + inversion H4. rewrite H0 in *. rewrite H3 in H8. inversion H8...  
  - intros * IH * H_st1 H_st2.
    inversion H_st1; subst;
    inversion H_st2; subst;
    try (f_equal; eauto with local_hints).
    + inversion H0.
    + inversion H1.
    + eapply Subst.deterministic... 
  - intros * IH1 * IH2 * IH3 * H_st1 H_st2.
    inversion H_st1; subst.
    + inversion H_st2; subst.
      * f_equal...  
      * exfalso; eapply not_value...
      * exfalso; eapply not_value with (e:= e0)...
      * inversion H3; subst. 
        exfalso; eapply not_value with (e:= v)...
      * inversion H3; subst. 
        exfalso; eapply not_value with (e:= v)...
    + inversion H_st2; subst.
      * exfalso; eapply not_value...
      * f_equal...
      * exfalso; eapply not_value...
      * exfalso; eapply not_value with (e:=case_left)...
      * exfalso; eapply not_value with (e:=case_left)...
    + inversion H_st2; subst.
      * exfalso; eapply not_value with (e := e0)...
      * exfalso; eapply not_value with (e := case_left)...
      * f_equal...
      * exfalso; eapply not_value...
      * exfalso; eapply not_value...
    + inversion H_st2; subst...
      * inversion H6; subst. 
        exfalso; eapply not_value with (e := v)...
      * exfalso; eapply not_value with (e := case_left)...
      * exfalso; eapply not_value with (e := case_right)...
        
    + inversion H_st2; subst...
      * inversion H6; subst. 
        exfalso; eapply not_value with (e := v)...
      * exfalso; eapply not_value with (e := case_left)...
      * exfalso; eapply not_value with (e := case_right)...
  - intros * IH1 * IH2 * IH3 * H_st1 H_st2.
    inversion H_st1; subst.
    + inversion H_st2; subst; try (f_equal; eauto with local_hints; fail);
      try (exfalso; eapply not_value; eauto with local_hints; fail);
      try (
          inversion H3; 
          exfalso; eapply not_value with (e := v); eauto with local_hints).
    + inversion H_st2; subst; try (f_equal; eauto with local_hints; fail);
      try (exfalso; eapply not_value; eauto with local_hints; fail);
      try (exfalso; eapply not_value_lsexpr; eauto with local_hints; fail).
    + inversion H_st2; subst; try (f_equal; eauto with local_hints; fail);
      try (exfalso; eapply not_value; eauto with local_hints; fail);
      try (exfalso; eapply not_value_lsexpr; eauto with local_hints; fail).
    + inversion H_st2; subst.
      * inversion H7; subst.
        exfalso; eapply not_value with (e:=v)...
      * inversion H7; subst.
        exfalso; eapply not_value_lsexpr...
      * exfalso; eapply not_value with (e:=default)...
      * rewrite H6 in H11. inversion H11. f_equal...
      * rewrite H6 in H11. inversion H11. 
    + inversion H_st2; subst; try (f_equal; eauto with local_hints; fail);
      try (exfalso; eapply not_value_lsexpr; eauto with local_hints; fail).
      * inversion H7; subst.
        exfalso; eapply not_value with(e:=v)...
      * exfalso; eapply not_value with (e:=e'₁)...
      * rewrite H6 in H11; inversion H11.
Qed.
