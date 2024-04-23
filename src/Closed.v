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


Fixpoint is_free_in (x : string) (e : expr) : Prop :=
  match e with 
  | <{#y}> => x = y
  | <{e₁ e₂}> 
  | <{e₁ - e₂}>  
  | <{e₁ == e₂}>  
  | <{(e₁, e₂)}>  => is_free_in x e₁ \/ is_free_in x e₂
  | <{fun y : _ => e}> => ¬ (x = y) /\ is_free_in x e
  | <{true}> | <{false}> | E_Num _ | <{ unit }> => False
  | <{if e₁ then e₂ else e₃}> 
  | <{match e₁ with | inl => e₂ | inr => e₃ end}> => is_free_in x e₁ \/ is_free_in x e₂ \/ is_free_in x e₃
  | <{let y = e₁ in e₂}> => 
      is_free_in x e₁ \/ ¬ (x = y) /\ is_free_in x e₂
  | <{first e}> | <{second e}> 
  | <{ e::_ }> | <{fix e}> 
  | <{ inl < _ | _> e }> | <{ inr < _ | _> e }> 
  |  <{_[e]}> => is_free_in x e
  | <{ { lse } }> => is_free_in_lsexpr x lse
  | <{match_sum e with ls : default end_sum}> => 
    is_free_in x e \/ is_free_in x default \/ is_free_in_lsexpr x ls
  end
with 
  is_free_in_lsexpr (x : string) (lse : lsexpr) := 
  match lse with 
  | <{ nil }> => False
  | <{ _ := e; tail }> => is_free_in x e \/ is_free_in_lsexpr x tail
  end
  .

Hint Unfold is_free_in : local_hints.
Hint Unfold is_free_in_lsexpr : local_hints.

Definition closed e := ∀ x, ¬ is_free_in x e.
Definition closed_lsexpr e := ∀ x, ¬ is_free_in_lsexpr x e.

Hint Unfold closed : local_hints.
Hint Unfold closed_lsexpr : local_hints.

Lemma free_has_type :
    ∀ e, ∀ Γ Σ t x,
    is_free_in x e ->
    has_type Σ Γ e t ->  
    ∃ tₓ, Γ ? x = Some tₓ.
Proof with eauto with local_hints.
  pose (
    P (e : expr) := 
      ∀ Γ Σ t x,
      is_free_in x e ->
      has_type Σ Γ e t ->  
      ∃ tₓ, Γ ? x = Some tₓ
  ). 
  pose (
    P0 (branches : lsexpr) :=
      ∀ Σ Γ x,
        is_free_in_lsexpr x branches ->
        (
          ∀ name_sum t,
          Σ / Γ |-ₛ name_sum ~> branches : t ->  
          ∃ tₓ, Γ ? x = Some tₓ
        ) /\
        (
          ∀ t,
          Σ / Γ |-ᵣ branches : t ->  
          ∃ tₓ, Γ ? x = Some tₓ
        )
  ).

  intro e.
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0; clear e P P0;
  try (intros * IH1 * IH2 * IH3 * H_free H_type);
  try (intros * IH1 * IH2 * H_free H_type);
  try (intros * IH1 * IH2 * H_free; split; intros * H_type);
  try (intros * IH1 *  H_free H_type);
  try (intros * H_free H_type);
  try (inversion H_free; try inversion H; inversion H_type; subst; eauto with local_hints; fail);
  try (simpl in H_free; inversion H_type; eauto with local_hints; fail);
  try (inversion H_free; inversion H_type; subst;
    destruct (IH2 Σ Γ _ H); eauto with local_hints; fail
    ).
  - inversion H_free; inversion H_type; subst.
    eapply IH1 with (Σ := Σ) (Γ := (x |-> t; Γ)) in H7...
    destruct H7 as [tₓ Ht_x].
    exists tₓ.
    rewrite <- Ht_x.
    rewrite Maps.update_neq...
  - inversion H_free; 
    inversion H_type;
    subst.
    + eapply IH1 with (Σ := Σ) (Γ := Γ) in H6...
    + destruct H. eapply IH2 with (Σ := Σ) (Γ := (x |-> t₁; Γ)) in H7...
      destruct H7 as [tₓ Ht_x].
      exists tₓ.
      rewrite <- Ht_x.
      rewrite Maps.update_neq...
  - simpl in H_free; inversion H_type; subst.
    destruct (IH1 Σ Γ _ H_free)...
  - inversion H_free; inversion H_type; try inversion H; subst...
    destruct (IH3 Σ Γ _ H9)...
  - intros * H_free.
    inversion H_free.
  - inversion H_free; 
    inversion H_type;
    subst...
    edestruct IH2 as [H' _]...
  - inversion H_free; 
    inversion H_type;
    subst...
    edestruct IH2 as [_ H']...
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
      ∀ Σ,
        (
          ∀ name_sum t,
          Σ / empty |-ₛ name_sum ~> branches : t ->  
          closed_lsexpr branches
        ) /\ (
          ∀ t,
          Σ / empty |-ᵣ branches : t ->  
          closed_lsexpr branches
        ) 
  ).
  intro e.
  apply expr_mut_ind with (P := P) (P0 := P0);
  unfold P; unfold P0; clear e P P0;
  try (
    intros * IH1 * IH2 * H_type x_contra H_contra;
    inversion H_contra; inversion H_type; subst;
    try (eapply IH1; eauto with local_hints; fail);
    try (eapply IH2; eauto with local_hints; fail);
    fail
  );
  try (
    intros * IH1 * IH2 * IH3 * H_type x_contra H_contra;
    inversion H_type; subst;
    inversion H_contra;
    try (eapply IH1; eauto with local_hints; fail);
    try inversion H;
    try (eapply IH2; eauto with local_hints; fail);
    try (eapply IH3; eauto with local_hints; fail);
    fail
  );
  try (
    intros * IH1 * H_type x_contra H_contra;
    inversion H_type; subst;
    simpl in H_contra;
    eapply IH1; eauto with local_hints;
    fail
  )...
  - intros * H_type x_contra H_contra. inversion H_type; subst. inversion H2.
  - intros * IH1 * H_type x_contra H_contra.
    eapply free_has_type in H_contra as [t_x H_eq]...
    inversion H_eq.
  - intros * IH1 * IH2 * H_type x_contra H_contra.
    inversion H_contra; inversion H_type; subst.
    + eapply (IH1 _ _ H6)...
    + eapply free_has_type in H_contra as [t_x H_eq]...
      inversion H_eq.
  - intros * IH1 * IH2 * IH3 * H_type x_contra H_contra.
    inversion H_contra; inversion H_type; subst...
    + eapply IH1... 
    + inversion H.
      * eapply IH2... 
      * destruct IH3 with (Σ := Σ) as [IH3' _]; eapply IH3'... 
  - intros *; split; intros * H_type...
  - intros * IH1 * IH2 *; split; intros * H_type x_contra H_contra;
    inversion H_type;
    destruct H_contra; subst;
    try (eapply IH1; eauto with local_hints; fail)...
    + destruct IH2 with (Σ := Σ) as [H _].
      eapply H...
    + destruct IH2 with (Σ := Σ) as [_ H].
      eapply H...
Qed. 


Hint Resolve typed_empty : local_hints.

Ltac closed_inv :=
  intros * H;
  unfold closed in *;
  repeat split; 
    intros x_contra H_contra;
    apply H with x_contra;
    eauto with local_hints.

Lemma closed_app : 
  ∀ e₁ e₂, 
  closed (E_App e₁ e₂) -> 
  closed e₁ /\ closed e₂.
Proof ltac:(closed_inv).

Hint Resolve closed_app : local_hints.



Lemma closed_let : 
  ∀ x e₁ e₂, 
  closed (E_Let x e₁ e₂) -> 
  closed e₁.
Proof ltac:(closed_inv).

Hint Resolve closed_let : local_hints.


Lemma closed_if : 
  ∀ e₁ e₂ e₃, 
  closed (E_If e₁ e₂ e₃) -> 
  closed e₁ /\ closed e₂ /\ closed e₃.
Proof ltac:(closed_inv).

Hint Resolve closed_if : local_hints.


Lemma closed_minus : 
  ∀ e₁ e₂, 
  closed (E_Minus e₁ e₂) -> 
  closed e₁ /\ closed e₂.
Proof ltac:(closed_inv).

Hint Resolve closed_minus : local_hints.

Lemma closed_eq : 
  ∀ e₁ e₂, 
  closed (E_Eq e₁ e₂) -> 
  closed e₁ /\ closed e₂.
Proof ltac:(closed_inv).

Hint Resolve closed_eq : local_hints.

Lemma closed_pair : 
  ∀ e₁ e₂, 
  closed (E_Pair e₁ e₂) -> 
  closed e₁ /\ closed e₂.
Proof ltac:(closed_inv).

Hint Resolve closed_pair : local_hints.

Lemma closed_first : 
  ∀ e, 
  closed (E_First e) -> 
  closed e.
Proof ltac:(closed_inv).
Hint Resolve closed_first : local_hints.



Lemma closed_second : 
  ∀ e, 
  closed (E_Second e) -> 
  closed e.
Proof ltac:(closed_inv).
Hint Resolve closed_second : local_hints.


Lemma closed_record : 
  ∀ x e tail, 
  closed_lsexpr (LSE_Cons x e tail) -> 
  closed e /\ closed_lsexpr tail.
Proof ltac:(closed_inv).
Hint Resolve closed_record : local_hints.


Lemma closed_access : 
  ∀ x e, 
  closed <{e :: x}> -> 
  closed e.
Proof ltac:(closed_inv).
Hint Resolve closed_access : local_hints.


Lemma closed_fix : 
  ∀ e, 
  closed (E_Fix e) -> 
  closed e.
Proof ltac:(closed_inv).
Hint Resolve closed_fix : local_hints.


Lemma closed_in_left :
  ∀ e t₁ t₂,
  closed (E_In_Left t₁ t₂ e) ->  
  closed e.
Proof ltac:(closed_inv).
Hint Resolve closed_in_left : local_hints.

Lemma closed_in_right :
  ∀ e t₁ t₂,
  closed (E_In_Right t₁ t₂ e) ->  
  closed e.
Proof ltac:(closed_inv).
Hint Resolve closed_in_right : local_hints.



Lemma closed_match :
  ∀ e e_left e_right,
  closed (E_Match e e_left e_right) -> 
  closed e /\ closed e_left /\ closed e_right.
Proof ltac:(closed_inv).
Hint Resolve closed_match : local_hints.

Lemma closed_sum_constr :
  ∀ constr e,
  closed <{constr[e]}> -> 
  closed e.
Proof ltac:(closed_inv).
Hint Resolve closed_sum_constr : local_hints.

Lemma closed_sum_match : 
  ∀ e default branches, 
  closed (E_Sum_Match e default branches) -> 
  closed e /\ closed default /\ closed_lsexpr branches.
Proof ltac:(closed_inv).

Hint Resolve closed_sum_match : local_hints.
