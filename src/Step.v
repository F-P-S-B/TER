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

Reserved Notation "x ->> y" (at level 70, no associativity).

Inductive step : expr -> expr -> Prop := 
  | ST_App_Fun : 
      ∀ (x : string) (t : type) (e e' v : expr),
      value v -> 
      substitution v x e e' ->
      (E_App (E_Fun x t e) v) ->> e'
  | ST_App_Left : 
      ∀ (e1 e1' e2 : expr),
      e1 ->> e1' ->
      (E_App e1 e2) ->> (E_App e1' e2)
  | ST_App_Right : 
      ∀ (v1 e2 e2' : expr),
      value v1 ->
      e2 ->> e2' ->
      (E_App v1 e2) ->> (E_App v1 e2')
  | ST_If_True : 
      ∀ (e1 e2 : expr),
      (E_If E_True e1 e2) ->> e1
  | ST_If_False : 
      ∀ (e1 e2 : expr),
      (E_If E_False e1 e2) ->> e2
  | ST_If : 
      ∀ (e1 e1' e2 e3 : expr),
      e1 ->> e1' ->
      (E_If e1 e2 e3) ->> (E_If e1' e2 e3)
  | ST_Let_Left : 
      ∀ (x : string) (e1 e1' e2 : expr),
      e1 ->> e1' ->
      (E_Let x e1 e2) ->> (E_Let x e1' e2)
  | ST_Let_Right : 
      ∀ (x : string) (v1 e2 e2' : expr),
      value v1 ->
      substitution v1 x e2 e2' ->
      (E_Let x v1 e2) ->> e2'
  | ST_Minus_Left :  
      ∀ (e1 e1' e2 : expr),
      e1 ->> e1' ->
      (E_Minus e1 e2) ->> (E_Minus e1' e2)
  | ST_Minus_Right :  
      ∀ (v1 e2 e2' : expr),
      value v1 ->
      e2 ->> e2' ->
      (E_Minus v1 e2) ->> (E_Minus v1 e2')
  | ST_Minus_Num : 
      ∀ (z1 z2 : Z),
      (E_Minus (E_Num z1) (E_Num z2)) ->> (E_Num (z1 - z2))

  | ST_Eq_Left :  
      ∀ (e1 e1' e2 : expr),
      e1 ->> e1' ->
      (E_Eq e1 e2) ->> (E_Eq e1' e2)
  | ST_Eq_Right :  
      ∀ (v1 e2 e2' : expr),
      value v1 ->
      e2 ->> e2' ->
      (E_Eq v1 e2) ->> (E_Eq v1 e2')
  | ST_Eq_Num_Eq : 
      ∀ (z : Z),
      (E_Eq (E_Num z) (E_Num z)) ->> (E_True)
  | ST_Eq_Num_Neq : 
      ∀ (z1 z2 : Z),
      z1 <> z2 ->
      (E_Eq (E_Num z1) (E_Num z2)) ->> (E_False)


  | ST_Pair_Left :  
      ∀ (e1 e1' e2 : expr),
      e1 ->> e1' ->
      (E_Pair e1 e2) ->> (E_Pair e1' e2)
  | ST_Pair_Right :  
      ∀ (v1 e2 e2' : expr),
      value v1 ->
      e2 ->> e2' ->
      (E_Pair v1 e2) ->> (E_Pair v1 e2')
  | ST_First :  
      ∀ (e e' : expr),
      e ->> e' ->
      (E_First e) ->> (E_First e')
  | ST_Second :  
      ∀ (e e' : expr),
      e ->> e' ->
      (E_Second e) ->> (E_Second e')
  | ST_First_Pair :  
      ∀ (v₁ v₂ : expr),
      value v₁ -> 
      value v₂ ->
      (E_First (E_Pair v₁ v₂)) ->> v₁
  | ST_Second_Pair :  
      ∀ (v₁ v₂ : expr),
      value v₁ -> 
      value v₂ ->
      (E_Second (E_Pair v₁ v₂)) ->> v₂
  
  | ST_Record_Tail : 
      ∀ x e tail tail', 
      tail ->> tail' -> 
      (E_Record_Cons x e tail) ->> (E_Record_Cons x e tail')
  
  | ST_Record : 
      ∀ x e e' tail,
      value tail -> 
      e ->> e' -> 
      (E_Record_Cons x e tail) ->> (E_Record_Cons x e' tail)
  
  | ST_Access : 
      ∀ x e e',
      e ->> e' ->
      (E_Record_Access e x) ->> (E_Record_Access e' x)

  | ST_Access_Value : 
      ∀ x e v,
      value e -> 
      lookup_val_record x e = Some v ->
      (E_Record_Access e x) ->> v

  | ST_Fix :
      ∀ (e e': expr),
      e ->> e' ->
      (E_Fix e) ->> (E_Fix e')
  
  | ST_Fix_Fun :
      ∀ x t e e',
      substitution (E_Fix (E_Fun x t e)) x e e' ->
      (E_Fix (E_Fun x t e)) ->> e'

where 
    "x ->> y" := (step x y)
.

Hint Constructors step : local_hints.



Local Lemma not_value: 
  ∀ e e',
  value e -> 
  ~ e ->> e'.
Proof.
  induction e; intros e' H_val H_contra;
  try (inversion H_val; inversion H_contra; fail).
  inversion H_val; subst.
  inversion H_contra; subst.
  - apply IHe1 with e1'; auto.
  - apply IHe2 with e2'; auto.
  - inversion H_val; subst; inversion H_contra; subst.
    + eapply IHe2; eauto.
    + eapply IHe1; eauto.
Qed.



Local Theorem deterministic :
    ∀ e e'₁ e'₂, 
    e ->> e'₁ ->
    e ->> e'₂ ->
    e'₁ = e'₂.
Proof with eauto with local_hints.
  induction e; 
  intros * H_s_1 H_s_2;
  try (inversion H_s_1; inversion H_s_2; fail).
  - inversion H_s_1; inversion H_s_2; subst;
    try (exfalso; eapply not_value; eauto with local_hints; fail).
    
    + eapply Subst.deterministic; inversion H4; subst...
    + inversion H7.
    + exfalso. eapply not_value; try apply H1...
    + inversion H2. 
    + f_equal. apply IHe1...
    + f_equal. apply IHe2...
  - inversion H_s_1; inversion H_s_2; subst;
    try (inversion H3; fail);
    try (inversion H4; fail);
    try (inversion H7; fail)...
    f_equal...
  - inversion H_s_1; inversion H_s_2; subst;
    try 
      (exfalso; eapply not_value;
       eauto with local_hints; fail).
    + f_equal...
    + eapply Subst.deterministic...
  - inversion H_s_1; inversion H_s_2; subst;
    try 
      (exfalso; eapply not_value;
       eauto with local_hints; fail);
    try (
      f_equal; eauto with local_hints; 
      try apply IHe1; eauto with local_hints;
      try apply IHe2; eauto with local_hints;
      fail
    ).
    + inversion H2.
    + inversion H3.
    + inversion H5.
    + inversion H6.
    + inversion H3. inversion H4; subst. reflexivity.
  - inversion H_s_1; inversion H_s_2; subst;
    try 
      (exfalso; eapply not_value;
       eauto with local_hints; fail);
    try (
      f_equal; eauto with local_hints; 
      try apply IHe1; eauto with local_hints;
      try apply IHe2; eauto with local_hints;
      fail
    );
    try (inversion H2; fail);
    try (inversion H3; fail);
    try (inversion H5; fail);
    try (inversion H6; fail);
    try (inversion H7; fail).
    + inversion H. inversion H4; subst. contradiction.
    + inversion H4. inversion H5; subst. contradiction.
  - inversion H_s_1; inversion H_s_2; subst;
    try 
      (exfalso; eapply not_value;
       eauto with local_hints; fail);
    try (
      f_equal; eauto with local_hints; 
      try apply IHe1; eauto with local_hints;
      try apply IHe2; eauto with local_hints;
      fail
    );
    try (inversion H2; fail);
    try (inversion H3; fail);
    try (inversion H5; fail);
    try (inversion H6; fail);
    try (inversion H7; fail).
  - inversion H_s_1; inversion H_s_2; subst;
    try 
      (exfalso; eapply not_value;
       eauto with local_hints; fail);
    try (
      f_equal; eauto with local_hints; 
      try apply IHe1; eauto with local_hints;
      try apply IHe2; eauto with local_hints;
      fail
    );
    try (inversion H2; fail);
    try (inversion H3; fail);
    try (inversion H5; fail);
    try (inversion H6; fail);
    try (inversion H7; fail).
    + exfalso. eapply not_value.
      apply V_Pair. apply H3. apply H4.
      eauto. 
    + exfalso. eapply not_value.
      apply V_Pair. apply H0. apply H1.
      eauto.
    + inversion H3; subst...  
  - inversion H_s_1; inversion H_s_2; subst;
    try 
      (exfalso; eapply not_value;
       eauto with local_hints; fail);
    try (
      f_equal; eauto with local_hints; 
      try apply IHe1; eauto with local_hints;
      try apply IHe2; eauto with local_hints;
      fail
    );
    try (inversion H2; fail);
    try (inversion H3; fail);
    try (inversion H5; fail);
    try (inversion H6; fail);
    try (inversion H7; fail).
    + exfalso. eapply not_value.
      apply V_Pair. apply H3. apply H4.
      eauto. 
    + exfalso. eapply not_value.
      apply V_Pair. apply H0. apply H1.
      eauto.
    + inversion H3; subst...
  - inversion H_s_1; inversion H_s_2; subst;
    try 
      (exfalso; eapply not_value;
       eauto with local_hints; fail);
    try (
      f_equal; eauto with local_hints; 
      try apply IHe1; eauto with local_hints;
      try apply IHe2; eauto with local_hints;
      fail
    );
    try (inversion H2; fail);
    try (inversion H3; fail);
    try (inversion H5; fail);
    try (inversion H6; fail);
    try (inversion H7; fail).
  - inversion H_s_1; inversion H_s_2; subst;
    try 
      (exfalso; eapply not_value;
       eauto with local_hints; fail);
    try (
      f_equal; eauto with local_hints; 
      try apply IHe1; eauto with local_hints;
      try apply IHe2; eauto with local_hints;
      fail
    );
    try (inversion H2; fail);
    try (inversion H3; fail);
    try (inversion H5; fail);
    try (inversion H6; fail);
    try (inversion H7; fail).
    rewrite H8 in H3. inversion H3... 
  - inversion H_s_1; inversion H_s_2; subst;
    try 
      (exfalso; eapply not_value;
       eauto with local_hints; fail);
    try (
      f_equal; eauto with local_hints; 
      try apply IHe1; eauto with local_hints;
      try apply IHe2; eauto with local_hints;
      fail
    );
    try (inversion H2; fail);
    try (inversion H3; fail);
    try (inversion H5; fail);
    try (inversion H6; fail);
    try (inversion H7; fail).
    + inversion H_s_1; subst. inversion H2. inversion H0.
    + inversion H2; subst.
      eapply Subst.deterministic...    
Qed.