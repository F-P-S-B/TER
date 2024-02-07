From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Hints.
Require Import Syntax.
Require Import Types.
Require Maps.
Import Maps.Notations.

(* 
Variable libre:
x libre dans e si 
e = Var x
e = App e1 e2 => x libre dans e1 ou x libre dans e2
e = λ y : t . e => y <> x et x libre dans e
e = If e1 e2 e3 => x libre dans e1 ou x libre dans e2 ou x libre dans e3
e = Let y e1 e2 => x libre dans e1 ou x <> y et x libre dans e2
e = Minus e1 e2 => x libre dans e1 ou x libre dans e2
 *)

Inductive is_free_in (x : string) : expr -> Prop :=
  | Free_Var : is_free_in x (E_Var x)
  | Free_App_Left : 
      ∀ e₁ e₂, 
      is_free_in x e₁ -> 
      is_free_in x (E_App e₁ e₂) 
  | Free_App_Right : 
      ∀ e₁ e₂, 
      is_free_in x e₂ -> 
      is_free_in x (E_App e₁ e₂) 
  | Free_Fun : 
      ∀ y t e, 
      y <> x -> 
      is_free_in x e -> 
      is_free_in x (E_Fun y t e) 
  | Free_If_Cond : 
      ∀ e₁ e₂ e₃, 
      is_free_in x e₁ -> 
      is_free_in x (E_If e₁ e₂ e₃) 
  | Free_If_Left : 
      ∀ e₁ e₂ e₃, 
      is_free_in x e₂ -> 
      is_free_in x (E_If e₁ e₂ e₃) 
  | Free_If_Right : 
      ∀ e₁ e₂ e₃, 
      is_free_in x e₃ -> 
      is_free_in x (E_If e₁ e₂ e₃) 
  | Free_Let_Left : 
      ∀ y e₁ e₂, 
      is_free_in x e₁ -> 
      is_free_in x (E_Let y e₁ e₂) 
  | Free_Let_Right : 
      ∀ y e₁ e₂, 
      y <> x -> is_free_in x e₂ -> 
      is_free_in x (E_Let y e₁ e₂) 
  | Free_Minus_Left : 
      ∀ e₁ e₂, 
      is_free_in x e₁ -> 
      is_free_in x (E_Minus e₁ e₂) 
  | Free_Minus_Right : 
      ∀ e₁ e₂, 
      is_free_in x e₂ -> 
      is_free_in x (E_Minus e₁ e₂) 
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
.

Hint Constructors is_free_in : local_hints.

Definition closed e := ∀ x, ~ is_free_in x e.

Lemma free_has_type :
    ∀ Γ e t x,
    is_free_in x e ->
    has_type Γ e t -> 
    ∃ t_x, Γ ? x = Some t_x.
Proof.
  intros * H_free H_type.
  generalize dependent Γ.
  generalize dependent t.
  induction H_free; intros;
  try (inversion H_type; subst; try eauto; fail);
  try (inversion H_type; subst; erewrite <- Maps.update_neq; eauto; fail).
Qed. 

Hint Resolve free_has_type : local_hints.


Theorem typed_empty :
    ∀ e t,
    has_type empty e t -> 
    closed e.
Proof.
    intros * H_type x H_contra.
    generalize dependent t.
    induction H_contra; intros;
    try (inversion H_type; subst; eauto; fail).
    - inversion H_type; subst. inversion H1.
    - inversion H_type; subst. 
      eapply free_has_type in H_contra; eauto.
      inversion H_contra. rewrite Maps.update_neq in H0; eauto. inversion H0.
    - inversion H_type; subst. 
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
