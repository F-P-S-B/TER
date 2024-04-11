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
      (E_App (E_Fun x t e) v) --> e'
  | ST_App_Left : 
      ∀ (e1 e1' e2 : expr),
      e1 --> e1' ->
      (E_App e1 e2) --> (E_App e1' e2)
  | ST_App_Right : 
      ∀ (v1 e2 e2' : expr),
      value v1 ->
      e2 --> e2' ->
      (E_App v1 e2) --> (E_App v1 e2')
  | ST_App_Exn_Left :
      ∀ (exn : exception) (e : expr),
      E_App (E_Exception exn) e --> (E_Exception exn)
  | ST_App_Exn_Right :
      ∀ (exn : exception) (v : expr),
      value v ->
      E_App v (E_Exception exn) --> E_App v (E_Exception exn)

  | ST_If_True : 
      ∀ (e1 e2 : expr),
      (E_If E_True e1 e2) --> e1
  | ST_If_False : 
      ∀ (e1 e2 : expr),
      (E_If E_False e1 e2) --> e2
  | ST_If : 
      ∀ (e1 e1' e2 e3 : expr),
      e1 --> e1' ->
      (E_If e1 e2 e3) --> (E_If e1' e2 e3)
  | ST_If_Exn :
    ∀ (exn : exception) (e_true e_false : expr),
    <{if `E_Exception exn` then e_true else e_false}> --> (E_Exception exn)


  | ST_Let_Left : 
      ∀ (x : string) (e1 e1' e2 : expr),
      e1 --> e1' ->
      (E_Let x e1 e2) --> (E_Let x e1' e2)
  | ST_Let_Right : 
      ∀ (x : string) (v1 e2 e2' : expr),
      value v1 ->
      substitution v1 x e2 e2' ->
      (E_Let x v1 e2) --> e2'
  | ST_Let_Exn  :
      ∀ (x : string) (exn : exception) (e : expr),
      <{let x = `E_Exception exn` in e}> --> E_Exception exn

      
  | ST_Minus_Left :  
      ∀ (e1 e1' e2 : expr),
      e1 --> e1' ->
      (E_Minus e1 e2) --> (E_Minus e1' e2)
  | ST_Minus_Right :  
      ∀ (v1 e2 e2' : expr),
      value v1 ->
      e2 --> e2' ->
      (E_Minus v1 e2) --> (E_Minus v1 e2')
  | ST_Minus_Num : 
      ∀ (z1 z2 : Z),
      (E_Minus (E_Num z1) (E_Num z2)) --> (E_Num (z1 - z2))
  | ST_Minus_Left_Exn :
      ∀ (exn : exception) (e : expr),
      <{ `E_Exception exn` - e }> --> E_Exception exn 
  | ST_Minus_Right_Exn :
      ∀ (exn : exception) (v : expr),
      value v ->
      <{ v - `E_Exception exn` }> --> E_Exception exn

  | ST_Eq_Left :  
      ∀ (e1 e1' e2 : expr),
      e1 --> e1' ->
      (E_Eq e1 e2) --> (E_Eq e1' e2)
  | ST_Eq_Right :  
      ∀ (v1 e2 e2' : expr),
      value v1 ->
      e2 --> e2' ->
      (E_Eq v1 e2) --> (E_Eq v1 e2')
  | ST_Eq_Num_Eq : 
      ∀ (z : Z),
      (E_Eq (E_Num z) (E_Num z)) --> (E_True)
  | ST_Eq_Num_Neq : 
      ∀ (z1 z2 : Z),
      z1 <> z2 ->
      (E_Eq (E_Num z1) (E_Num z2)) --> (E_False)
  | ST_Eq_Left_Exn :
      ∀ (exn : exception) (e : expr),
      <{ `E_Exception exn` == e }> --> E_Exception exn 
  | ST_Eq_Right_Exn :
      ∀ (exn : exception) (v : expr),
      value v ->
      <{ v == `E_Exception exn` }> --> E_Exception exn

  | ST_Pair_Left :  
      ∀ (e1 e1' e2 : expr),
      e1 --> e1' ->
      (E_Pair e1 e2) --> (E_Pair e1' e2)
  | ST_Pair_Right :  
      ∀ (v1 e2 e2' : expr),
      value v1 ->
      e2 --> e2' ->
      (E_Pair v1 e2) --> (E_Pair v1 e2')
  | ST_Pair_Left_Exn :
      ∀ (exn : exception) (e : expr),
      <{ (`E_Exception exn`, e) }> --> E_Exception exn 
  | ST_Pair_Right_Exn :
      ∀ (exn : exception) (v : expr),
      value v ->
      <{ (v, `E_Exception exn`) }> --> E_Exception exn


  | ST_First :  
      ∀ (e e' : expr),
      e --> e' ->
      (E_First e) --> (E_First e')
  | ST_First_Pair :  
      ∀ (v₁ v₂ : expr),
      value v₁ -> 
      value v₂ ->
      (E_First (E_Pair v₁ v₂)) --> v₁
  | ST_First_Exn :
      ∀ (exn : exception),
      <{first `E_Exception exn`}> --> E_Exception exn

  | ST_Second :  
      ∀ (e e' : expr),
      e --> e' ->
      (E_Second e) --> (E_Second e')
  | ST_Second_Pair :  
      ∀ (v₁ v₂ : expr),
      value v₁ -> 
      value v₂ ->
      (E_Second (E_Pair v₁ v₂)) --> v₂
  | ST_Second_Exn :
      ∀ (exn : exception),
      <{second `E_Exception exn`}> --> E_Exception exn

  | ST_Record_Tail : 
      ∀ x e tail tail', 
      blocking_expr e -> 
      tail --> tail' -> 
      (E_Record_Cons x e tail) --> (E_Record_Cons x e tail')
  
  | ST_Record_Cons : 
      ∀ x e e' tail,
      e --> e' -> 
      (E_Record_Cons x e tail) --> (E_Record_Cons x e' tail)      
  
  | ST_Access : 
      ∀ x e e',
      e --> e' ->
      (E_Record_Access e x) --> (E_Record_Access e' x)

  | ST_Access_Value : 
      ∀ x e e',
      blocking_expr e -> 
      lookup_val_record x e = Some e' ->
      (E_Record_Access e x) --> e'

  | ST_Fix :
      ∀ (e e': expr),
      e --> e' ->
      (E_Fix e) --> (E_Fix e')
  
  | ST_Fix_Fun :
      ∀ x t e e',
      substitution (E_Fix (E_Fun x t e)) x e e' ->
      (E_Fix (E_Fun x t e)) --> e'
  | ST_Fix_Exn :
      ∀ (exn : exception) (e : expr),
      <{fix `E_Exception exn`}> --> E_Exception exn

  | ST_In_Left :
      ∀ t₁ t₂ e e', 
      e --> e' -> 
      E_In_Left t₁ t₂ e --> E_In_Left t₁ t₂ e'

  | ST_In_Right :
      ∀ t₁ t₂ e e', 
      e --> e' -> 
      E_In_Right t₁ t₂ e --> E_In_Right t₁ t₂ e'
  
  | ST_Match_Main :
      ∀ e e' e_left e_right,
      e --> e' ->
      E_Match e e_left e_right --> E_Match e' e_left e_right


  | ST_Match_Left :
      ∀ e e_left e_left' e_right,
      value e ->
      e_left --> e_left' -> 
      E_Match e e_left e_right --> E_Match e e_left' e_right

  | ST_Match_Right :
      ∀ e e_left e_right e_right',
      value e -> 
      value e_left -> 
      e_right --> e_right' -> 
      E_Match e e_left e_right --> E_Match e e_left e_right'

  | ST_Match_Left_App :
      ∀ t₁ t₂ e e_left e_right,
      value e -> 
      value e_left -> 
      value e_right -> 
      E_Match (E_In_Left t₁ t₂ e) e_left e_right --> E_App e_left e

  | ST_Match_Right_App :
    ∀ t₁ t₂ e e_left e_right,
    value e -> 
    value e_left -> 
    value e_right -> 
    E_Match (E_In_Right t₁ t₂ e) e_left e_right --> E_App e_right e

  | ST_Sum_Constr :
      ∀ constr e e',
      e --> e' -> 
      E_Sum_Constr constr e --> E_Sum_Constr constr e'
  | ST_Sum_Constr_Exn :
      ∀ constr exn,
      E_Sum_Constr constr (E_Exception exn) --> E_Exception exn

  | ST_Sum_Match_Main : 
      ∀ e e' branches, 
      e --> e' -> 
      (E_Sum_Match e branches) --> (E_Sum_Match e' branches)
  | ST_Sum_Match_Main_Exn : 
      ∀ exn branches, 
      (E_Sum_Match (E_Exception exn) branches) --> E_Exception exn
  | ST_Sum_Match :
      ∀ v branches branches', 
      value v -> 
      branches -->ₗ branches' ->
      (E_Sum_Match v branches) 
      --> (E_Sum_Match v branches')
  | ST_Sum_Match_Apply :
      ∀ constr v branches b, 
      value v -> 
      value_lsexpr branches ->
      lookup_constr constr branches = Some b ->
      (E_Sum_Match 
        (E_Sum_Constr constr v)
        branches
      ) 
      --> <{b v}>
  | ST_Sum_Match_Apply_Not_Found :
      ∀ constr v branches b, 
      value v -> 
      value_lsexpr branches ->
      lookup_constr constr branches = None ->
      (E_Sum_Match 
        (E_Sum_Constr constr v)
        branches
      ) 
      --> E_Exception Ex_Unhandled_Case

where
    "x --> y" := (step x y)
     
with step_lsexpr : lsexpr -> lsexpr -> Prop := 
  | ST_LSExpr_Cons :
      ∀ constr e e' branches,
      e --> e' -> 
      step_lsexpr 
        (LSE_Cons constr e branches) 
        (LSE_Cons constr e' branches)
  | ST_LSExpr_Tail :
      ∀ constr v branches branches',
      blocking_expr v -> 
      branches -->ₗ branches' ->
      (LSE_Cons constr v branches) -->ₗ (LSE_Cons constr v branches') 
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
  clear P P0;
  try (
    intros * H_val H_contra;
    inversion H_contra;
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
    intros * IH1 * IH2 * H_val H_contra;
    inversion H_val;
    inversion H_contra; subst;
    try (eapply IH1; eauto with local_hints; fail);
    try (eapply IH2; eauto with local_hints; fail);
    fail
  );
  try (
    intros * IH1 * IH2 * IH3 * H_val H_contra;
    inversion H_val;
    inversion H_contra; subst;
    try (eapply IH1; eauto with local_hints; fail);
    try (eapply IH2; eauto with local_hints; fail);
    try (eapply IH3; eauto with local_hints; fail);
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
    + inversion H_st2; subst.
      * eapply Subst.deterministic...
      * inversion H4.
      * eapply not_value in H5... contradiction.
    + inversion H_st1; subst; 
      try (
        inversion H_st2; subst;try (eapply Subst.deterministic; eauto with local_hints; fail); 
        try (inversion H0; fail);
        f_equal; eauto with local_hints;
        try (exfalso; eapply not_value; eauto with local_hints; fail);
        fail
      ).
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
      * exfalso; eapply not_value; eauto with local_hints.
      * inversion H2.
    + inversion H_st2; subst.
      * exfalso; eapply not_value; eauto with local_hints.
      * f_equal...
      * inversion H3.
    + inversion H_st2; subst...
      * inversion H2.
      * inversion H3.
  - intros * IH1 * IH2 * H_st1 H_st2.
    inversion H_st1; subst.
    + inversion H_st2; subst.
      * f_equal...
      * exfalso; eapply not_value; eauto with local_hints.
      * inversion H2.
      * inversion H2.
    + inversion H_st2; subst.
      * exfalso; eapply not_value; eauto with local_hints.
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
      * exfalso; eapply not_value with (e:=e'₂); eauto with local_hints.
      * exfalso; eapply not_value with (e:=v₂); eauto with local_hints.
    + inversion H2; subst.
      * exfalso; eapply not_value with (e:=e'₁); eauto with local_hints.
      * exfalso; eapply not_value with (e:=v₂); eauto with local_hints. 
  - intros * IH * H_st1 H_st2.
    inversion H_st1; subst;
    inversion H_st2; subst;
    try (f_equal; eauto with local_hints).
    + inversion H0; subst.
      * exfalso; eapply not_value with (e:=v₁); eauto with local_hints.
      * exfalso; eapply not_value with (e:=e'₂); eauto with local_hints.
    + inversion H2; subst.
      * exfalso; eapply not_value with (e:=v₁); eauto with local_hints.
      * exfalso; eapply not_value with (e:=e'₁); eauto with local_hints. 
  - intros * IH * H_st1 H_st2.
    inversion H_st1;
    inversion H_st2; subst.
    + f_equal... 
    + exfalso; eapply not_value; eauto with local_hints. 
    + exfalso; eapply not_value; eauto with local_hints. 
    + rewrite H3 in H8. inversion H8...  
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
      * exfalso; eapply not_value; eauto with local_hints.
      * exfalso; eapply not_value with (e:= e0); eauto with local_hints.
      * inversion H3; subst. 
        exfalso; eapply not_value with (e:= e1); eauto with local_hints.
      * inversion H3; subst. 
        exfalso; eapply not_value with (e:= e1); eauto with local_hints.
    + inversion H_st2; subst.
      * exfalso; eapply not_value; eauto with local_hints.
      * f_equal...
      * exfalso; eapply not_value; eauto with local_hints.
      * exfalso; eapply not_value with (e:=case_left); eauto with local_hints.
      * exfalso; eapply not_value with (e:=case_left); eauto with local_hints.
    + inversion H_st2; subst.
      * exfalso; eapply not_value with (e := e0); eauto with local_hints.
      * exfalso; eapply not_value with (e := case_left); eauto with local_hints.
      * f_equal...
      * exfalso; eapply not_value; eauto with local_hints.
      * exfalso; eapply not_value; eauto with local_hints.
    + inversion H_st2; subst.
      * inversion H6; subst. 
        exfalso; eapply not_value with (e := e1)...
      * exfalso; eapply not_value with (e := case_left)...
      * exfalso; eapply not_value with (e := case_right)...
      * eauto.
        
    + inversion H_st2; subst.
      * inversion H6; subst. 
        exfalso; eapply not_value with (e := e1)...
      * exfalso; eapply not_value with (e := case_left)...
      * exfalso; eapply not_value with (e := case_right)...
      * eauto.
  - intros * IH1 * IH2 * H_st1 H_st2.
    inversion H_st1; inversion H_st2; subst; 
    try (exfalso; eapply not_value; eauto with local_hints; fail);
    try (exfalso; eapply not_value_lsexpr; eauto with local_hints; fail).
    + apply (IH1 _ _ H2) in H6; subst...
    + inversion H2. exfalso; eapply not_value... 
    + apply (IH2 _ _ H3) in H8; subst...
    + inversion H8; subst...
      exfalso; eapply not_value...
    + inversion H5; f_equal; subst;rewrite H4 in H10; inversion H10... 
Qed.
