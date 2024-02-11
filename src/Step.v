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



