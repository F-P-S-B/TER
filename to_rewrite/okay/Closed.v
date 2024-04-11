From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Hints.
Require Import Syntax.
Require Import Types.
Require Maps.
Import Maps.Notations.
Require Import List.
Import ListNotations.

(* TODO: Branches des matchs *)
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
  
  | Free_Sum_Match_Base :
    ∀ e branches, 
    is_free_in x e -> 
    is_free_in x (E_Sum_Match e branches)

  | Free_Sum_Match_Rec_Branches :
    ∀ e branches,
    is_free_in_lsexpr x branches -> 
    is_free_in x (E_Sum_Match e branches)


with is_free_in_lsexpr  (x : string) : lsexpr -> Prop :=
  | Free_LSExpr_Cons :
    ∀ e constr tail,
    is_free_in x e -> 
    is_free_in_lsexpr x (LSE_Cons constr e tail)
  | Free_LSExpr_Tail :
    ∀ e constr tail,
    is_free_in_lsexpr x tail -> 
    is_free_in_lsexpr x (LSE_Cons constr e tail)
.

Hint Constructors is_free_in : local_hints.
Hint Constructors is_free_in_lsexpr : local_hints.

Definition closed e := ∀ x, ¬ is_free_in x e.
Definition closed_lsexpr e := ∀ x, ¬ is_free_in_lsexpr x e.

Hint Unfold closed : local_hints.
Hint Unfold closed_lsexpr : local_hints.

Lemma free_has_type :
    ∀ e, ∀ Γ Σ t x,
    is_free_in x e ->
    has_type Σ Γ e t ->  
    ∃ t_x, Γ ? x = Some t_x.
Proof with eauto with local_hints.
  pose (
    P (e : expr) := 
      ∀ Γ Σ t x,
      is_free_in x e ->
      has_type Σ Γ e t ->  
      ∃ t_x, Γ ? x = Some t_x
  ). 
  pose (
    P0 (branches : lsexpr) :=
      ∀ Γ Σ name_sum t x,
        is_free_in_lsexpr x branches ->
        has_type_lsexpr name_sum Σ Γ branches t ->  
        ∃ t_x, Γ ? x = Some t_x
  ).
  intro.
  apply expr_mut_ind with (P := P) (P0 := P0); 
  unfold P; unfold P0; intros;
  try (try inversion H; try inversion H0; try inversion H1; try inversion H2; try inversion H3; subst; eauto with local_hints; fail).
  - inversion H0; 
    inversion H1;
    subst.
    eapply H with (Σ := Σ) (Γ := (x |-> t; Γ)) in H6...
    destruct H6 as [t_x Ht_x].
    exists t_x.
    rewrite <- Ht_x.
    rewrite Maps.update_neq...
  - inversion H1; 
    inversion H2;
    subst.
    + eapply H with (Σ := Σ) (Γ := Γ) in H4...
    + eapply H0 with (Σ := Σ) (Γ := (x |-> t1; Γ)) in H7...
      destruct H7 as [t_x Ht_x].
      exists t_x.
      rewrite <- Ht_x.
      rewrite Maps.update_neq...
Qed.

Hint Resolve free_has_type : local_hints.


Theorem typed_empty :
    ∀ e, ∀ Σ t,
    has_type Σ empty e t ->  
    closed e.
Proof with eauto with local_hints.
  pose (
    P (e : expr) := 
      ∀ Σ t,
      has_type Σ empty e t ->  
      closed e
  ).
  pose (
    P0 (branches : lsexpr) :=
      ∀ name_sum Σ t,
        has_type_lsexpr name_sum Σ empty branches t ->  
        closed_lsexpr branches
  ).
  intro e.
  apply expr_mut_ind with (P := P) (P0 := P0);
  unfold P; unfold P0; intros; intros x_contra H_contra;
  try (inversion H_contra; fail).
  - inversion H. inversion H3.
  - inversion H1; subst. 
    inversion H_contra; subst.
    + eapply (H _ _ H8)...
    + eapply (H0 _ _ H6)...
  - inversion H_contra; inversion H0; subst.
    eapply free_has_type in H_contra as [t_x H_eq]...
    inversion H_eq.
  - inversion H_contra; inversion H2; subst.
    + eapply H in H4...        
    + eapply H0 in H4...        
    + eapply H1 in H4...
  - inversion H_contra; inversion H1; subst.
    + eapply (H _ _ H12)...
    + eapply free_has_type in H_contra as [t_x H_eq]...
      inversion H_eq.
  - inversion H_contra; inversion H1; subst.
    + eapply (H _ _ H9)...
    + eapply (H0 _ _ H11)...
  - inversion H_contra; inversion H1; subst.
    + eapply (H _ _ H9)...
    + eapply (H0 _ _ H11)...
  - inversion H_contra; inversion H1; subst.
    + eapply (H _ _ H9)...
    + eapply (H0 _ _ H11)...
  - inversion H_contra; inversion H0; subst.
    eapply (H _ _ H6)...
  - inversion H_contra; inversion H0; subst.
    eapply (H _ _ H6)...
  - inversion H_contra; inversion H1; subst.
    + eapply (H0 _ _ H13)...
    + eapply (H _ _ H11)...
  - inversion H_contra; inversion H0; subst.
    eapply (H _ _ H8)...
  - inversion H_contra; inversion H0; subst.
    eapply (H _ _ H6)...
  - inversion H_contra; inversion H0; subst.
    eapply (H _ _ H11)...
  - inversion H_contra; inversion H0; subst.
    eapply (H _ _ H11)...
  - inversion H_contra; inversion H2; subst.
    + eapply (H _ _ H12)...
    + eapply (H0 _ _ H14)...
    + eapply (H1 _ _ H15)...
  - inversion H_contra; inversion H0; subst.
    eapply (H _ _ H10)...
  - inversion H_contra; inversion H1; subst.
    + eapply (H _ _ H9)...
    + apply H0 in H11.
      eapply H11...
  - inversion H_contra; inversion H1; subst.
    + eapply (H _ _ H15)...
    + apply H0 in H12. eapply H12... 
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

Lemma closed_sum_match : 
  ∀ e branches, 
  closed (E_Sum_Match e branches) -> 
  closed e /\ closed_lsexpr branches.
Proof.
  intros.
  unfold closed in *.
  unfold closed_lsexpr in *.
  split;
    intros x H_contra;
    apply H with x;
    eauto with local_hints.
Qed.
