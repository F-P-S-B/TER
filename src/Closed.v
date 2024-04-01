From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Hints.
Require Import Syntax.
Require Import Types.
Require Maps.
Import Maps.Notations.

Inductive is_free_in (x : string) : expr -> Prop :=
  | Free_Var : is_free_in x <{x}>
  | Free_App_Left : 
      ∀ e₁ e₂, 
      is_free_in x e₁ -> 
      is_free_in x <{e₁ e₂}>
  | Free_App_Right : 
      ∀ e₁ e₂, 
      is_free_in x e₂ -> 
      is_free_in x <{e₁ e₂}>
  | Free_Fun : 
      ∀ y t e, 
      y <> x -> 
      is_free_in x e -> 
      is_free_in x <{fun y : t => e}> 
  | Free_If_Cond : 
      ∀ e₁ e₂ e₃, 
      is_free_in x e₁ -> 
      is_free_in x <{if e₁ then e₂ else e₃}> 
  | Free_If_Left : 
      ∀ e₁ e₂ e₃, 
      is_free_in x e₂ -> 
      is_free_in x <{if e₁ then e₂ else e₃}> 
  | Free_If_Right : 
      ∀ e₁ e₂ e₃, 
      is_free_in x e₃ -> 
      is_free_in x <{if e₁ then e₂ else e₃}> 
  | Free_Let_Left : 
      ∀ y e₁ e₂, 
      is_free_in x e₁ -> 
      is_free_in x <{let y = e₁ in e₂}>
  | Free_Let_Right : 
      ∀ y e₁ e₂, 
      y <> x -> is_free_in x e₂ -> 
      is_free_in x <{let y = e₁ in e₂}>
  | Free_Minus_Left : 
      ∀ e₁ e₂, 
      is_free_in x e₁ -> 
      is_free_in x <{e₁ - e₂}>
  | Free_Minus_Right : 
      ∀ e₁ e₂, 
      is_free_in x e₂ -> 
      is_free_in x <{e₁ - e₂}>

  | Free_Eq_Left : 
      ∀ e₁ e₂, 
      is_free_in x e₁ -> 
      is_free_in x <{e₁ == e₂}>
  | Free_Eq_Right : 
      ∀ e₁ e₂, 
      is_free_in x e₂ -> 
      is_free_in x <{e₁ == e₂}>
  | Free_Pair_Left : 
      ∀ e₁ e₂, 
      is_free_in x e₁ -> 
      is_free_in x (E_Pair e₁ e₂) 
  | Free_Pair_Right : 
      ∀ e₁ e₂, 
      is_free_in x e₂ -> 
      is_free_in x (E_Pair e₁ e₂) 
  | Free_First : 
    ∀ e, 
    is_free_in x e -> 
    is_free_in x (E_First e)
  | Free_Second : 
    ∀ e, 
    is_free_in x e -> 
    is_free_in x (E_Second e)

  | Free_Record_Cons_tail :
    ∀ y e tail, 
    is_free_in x tail -> 
    is_free_in x (E_Record_Cons y e tail)
  | Free_Record_Cons_head :
    ∀ y e tail, 
    is_free_in x e -> 
    is_free_in x (E_Record_Cons y e tail)

  | Free_Record_Access :
    ∀ y e, 
      is_free_in x e -> 
      is_free_in x (E_Record_Access e y) 

  | Free_Fix :  
      ∀ e, 
      is_free_in x e -> 
      is_free_in x (E_Fix e) 

  | Free_In_Left :
      ∀ e t₁ t₂, 
      is_free_in x e ->
      is_free_in x (E_In_Left t₁ t₂ e)
  
  | Free_In_Right :
      ∀ e t₁ t₂, 
      is_free_in x e -> 
      is_free_in x (E_In_Right t₁ t₂ e)

  | Free_Match_Main :
      ∀ e e_left e_right, 
      is_free_in x e -> 
      is_free_in x (E_Match e e_left e_right)

  | Free_Match_Left :
      ∀ e e_left e_right, 
      is_free_in x e_left -> 
      is_free_in x (E_Match e e_left e_right)
  
  | Free_Match_Right :
      ∀ e e_left e_right, 
      is_free_in x e_right -> 
      is_free_in x (E_Match e e_left e_right)
  | Free_Sum_Constr :
      ∀ e constr, 
      is_free_in x e -> 
      is_free_in x (E_Sum_Constr constr e)
.

Hint Constructors is_free_in : local_hints.

Definition closed e := ∀ x, ¬ is_free_in x e.

Hint Unfold closed : local_hints.

Lemma free_has_type :
    ∀ Γ Σ e t x,
    is_free_in x e ->
    has_type Σ Γ  e  t ->  
    ∃ t_x, Γ ? x = Some t_x.
Proof.
  intros * H_free H_type.
  generalize dependent Γ.
  generalize dependent t.
  induction H_free; intros;
  inversion H_type; subst; eauto;
  erewrite <- Maps.update_neq; eauto.
Qed. 

Hint Resolve free_has_type : local_hints.


Theorem typed_empty :
    ∀ Σ e t,
    has_type Σ empty  e  t ->  
    closed e.
Proof.
    intros * H_type x H_contra.
    generalize dependent t.
    induction H_contra; intros;
    try (inversion H_type; subst; eauto; fail).
    - (* e = E_Var x *) 
      inversion H_type; subst. inversion H2.
    - (* e = E_fun y t e', x != y *)
      inversion H_type; subst. 
      eapply free_has_type with (Γ := (y |-> t; empty)) (t := t2) in H_contra as [t_x H_eq]; eauto.
      rewrite Maps.update_neq in H_eq; eauto. inversion H_eq.
    - (* e = E_let y e₁ e₂, x != y *) 
      inversion H_type; subst. 
      eapply free_has_type in H_contra; eauto.
      inversion H_contra. 
      rewrite Maps.update_neq in H0; eauto. inversion H0.
Qed.

Hint Resolve typed_empty : local_hints.


Lemma closed_app : 
  ∀ e₁ e₂, 
  closed (E_App e₁ e₂) -> 
  closed e₁ /\ closed e₂.
Proof.
  intros.
  unfold closed in *.
  split; 
    intros x H_contra;
    apply H with x;
    eauto with local_hints.
Qed.

Hint Resolve closed_app : local_hints.



Lemma closed_let : 
  ∀ x e₁ e₂, 
  closed (E_Let x e₁ e₂) -> 
  closed e₁.
Proof.
  intros.
  unfold closed in *.
  intros x' H_contra.
  apply H with x'.
  eauto with local_hints.
Qed.

Hint Resolve closed_let : local_hints.


Lemma closed_if : 
  ∀ e₁ e₂ e₃, 
  closed (E_If e₁ e₂ e₃) -> 
  closed e₁ /\ closed e₂ /\ closed e₃.
Proof.
  intros.
  unfold closed in *.
  repeat split;
    intros x H_contra;
    apply H with x;
    eauto with local_hints.
Qed.

Hint Resolve closed_if : local_hints.


Lemma closed_minus : 
  ∀ e₁ e₂, 
  closed (E_Minus e₁ e₂) -> 
  closed e₁ /\ closed e₂.
Proof.
  intros.
  unfold closed in *.
  split; 
    intros x H_contra;
    apply H with x;
    eauto with local_hints.
Qed.

Hint Resolve closed_minus : local_hints.

Lemma closed_eq : 
  ∀ e₁ e₂, 
  closed (E_Eq e₁ e₂) -> 
  closed e₁ /\ closed e₂.
Proof.
  intros.
  unfold closed in *.
  split; 
    intros x H_contra;
    apply H with x;
    eauto with local_hints.
Qed.

Hint Resolve closed_eq : local_hints.

Lemma closed_pair : 
  ∀ e₁ e₂, 
  closed (E_Pair e₁ e₂) -> 
  closed e₁ /\ closed e₂.
Proof.
  intros.
  unfold closed in *.
  split; 
    intros x H_contra;
    apply H with x;
    eauto with local_hints.
Qed.

Hint Resolve closed_pair : local_hints.

Lemma closed_first : 
  ∀ e, 
  closed (E_First e) -> 
  closed e.
Proof.
  intros.
  unfold closed in *.
  intros x' H_contra;
  apply H with x';
  eauto with local_hints.
Qed.
Hint Resolve closed_first : local_hints.



Lemma closed_second : 
  ∀ e, 
  closed (E_Second e) -> 
  closed e.
Proof.
  intros.
  unfold closed in *.
  intros x' H_contra;
  apply H with x';
  eauto with local_hints.
Qed.
Hint Resolve closed_second : local_hints.


Lemma closed_record : 
  ∀ x e₁ e₂, 
  closed (E_Record_Cons x e₁ e₂) -> 
  closed e₁ /\ closed e₂.
Proof.
  intros.
  unfold closed in *.
  split; 
    intros x' H_contra;
    apply H with x';
    eauto with local_hints.
Qed.
Hint Resolve closed_record : local_hints.


Lemma closed_access : 
  ∀ x e, 
  closed (E_Record_Access e x) -> 
  closed e.
Proof.
  intros.
  unfold closed in *.
  intros x' H_contra;
  apply H with x';
  eauto with local_hints.
Qed.
Hint Resolve closed_access : local_hints.


Lemma closed_fix : 
  ∀ e, 
  closed (E_Fix e) -> 
  closed e.
Proof.
  intros.
  unfold closed in *.
  intros x' H_contra;
  apply H with x';
  eauto with local_hints.
Qed.
Hint Resolve closed_fix : local_hints.


Lemma closed_in_left :
  ∀ e t₁ t₂,
  closed (E_In_Left t₁ t₂ e) ->  
  closed e.
Proof.
  intros.
  unfold closed in *.
  intros x' H_contra;
  apply H with x';
  eauto with local_hints.
Qed.
Hint Resolve closed_in_left : local_hints.

Lemma closed_in_right :
  ∀ e t₁ t₂,
  closed (E_In_Right t₁ t₂ e) ->  
  closed e.
Proof.
  intros.
  unfold closed in *.
  intros x' H_contra;
  apply H with x';
  eauto with local_hints.
Qed.
Hint Resolve closed_in_right : local_hints.



Lemma closed_match :
  ∀ e e_left e_right,
  closed (E_Match e e_left e_right) -> 
  closed e /\ closed e_left /\ closed e_right.
Proof.
  intros.
  unfold closed in *.
  repeat split;
    intros x' H_contra;
    apply H with x';
    eauto with local_hints.
Qed.
Hint Resolve closed_match : local_hints.

Lemma closed_sum_constr :
  ∀ constr e,
  closed (E_Sum_Constr constr e) -> 
  closed e.
Proof.
  intros.
  unfold closed in *.
    intros x' H_contra;
    apply H with x';
    eauto with local_hints.
Qed.
Hint Resolve closed_sum_constr : local_hints.