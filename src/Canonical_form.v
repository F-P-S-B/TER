From Coq Require Import Unicode.Utf8.
Require Import Hints.
Require Import Syntax.
Require Import Types.
Require Maps.

Local Lemma t_num : 
    ∀ Γ e,
    has_type Γ e Type_Num -> 
    value e ->
    ∃ z, e = E_Num z.
Proof.
    intros * H_type H_val.
    inversion H_val; eauto; 
    subst; inversion H_type.
Qed.

Hint Resolve t_num : local_hints.

Local Lemma t_bool : 
    ∀ Γ e,
    has_type Γ e Type_Bool -> 
    value e ->
    e = E_True \/ e = E_False.
Proof.
    intros * H_type H_val.
    inversion H_val; subst; auto;
    inversion H_type.
Qed.

Hint Resolve t_bool : local_hints.

Local Lemma t_fun : 
    ∀ Γ e t1 t2,
    has_type Γ e (Type_Fun t1 t2) -> 
    value e ->
    ∃ x e', e = E_Fun x t1 e'. 
Proof.
    intros * H_type H_val.
    inversion H_val; subst; try (inversion H_type; fail).
    inversion H_type; subst.
    eauto.
Qed.
Hint Resolve t_fun : local_hints.


Local Lemma t_pair :
    ∀ Γ e t₁ t₂,
    has_type Γ e (Type_Prod t₁ t₂) -> 
    value e ->
    ∃ e₁ e₂, e = E_Pair e₁ e₂.
Proof.
    intros * H_type H_val.
    inversion H_val; subst; try (inversion H_type; fail).
    eauto.
Qed. 
Hint Resolve t_pair : local_hints.


Local Lemma t_record_nil :
    ∀ Γ e,
    has_type Γ e Type_Record_Nil -> 
    value e ->
    e = E_Record_Nil.
Proof.
    intros * H_type H_val.
    inversion H_val; subst; try (inversion H_type; fail).
    reflexivity.
Qed. 

Hint Resolve t_record_nil : local_hints.


Local Lemma t_record_cons :
    ∀ Γ e x t_x t_tail,
    has_type Γ e (Type_Record_Cons x t_x t_tail) -> 
    value e ->
    ∃ e' e_tail, e = E_Record_Cons x e' e_tail.
Proof.
    intros * H_type H_val.
    inversion H_type; subst; try (inversion H_val; fail).
    eauto.
Qed. 

Hint Resolve t_record_cons : local_hints.


Local Lemma record_type_exists :
  ∀ Γ e t_rec t x, 
  value e ->
  has_type Γ e t_rec ->
  lookup_type_record x t_rec = Some t -> 
  ∃ e', lookup_val_record x e = Some e'.
Proof.
  intros Γ e t_rec.
  generalize dependent Γ.
  generalize dependent e.
  induction t_rec; intros;
  try (inversion H1; fail).
  simpl in H1.
  assert (H2 := H0). 
  apply t_record_cons in H0 as [e' [e_tail H_eq]]; 
  subst; eauto. 
  simpl.
  destruct (String.eqb_spec x0 x); eauto.
  inversion H; subst.
  inversion H2.
  eapply IHt_rec2; eauto.
Qed.


Lemma lookup_type_val :
  ∀ Γ x e e' t_e t_e',
  has_type Γ e t_e ->
  value e ->
  lookup_type_record x t_e = Some t_e' ->
  lookup_val_record x e = Some e' -> 
  has_type Γ e' t_e'.
Proof.
  intros Γ x e e' t_e.
  generalize dependent Γ. 
  generalize dependent x. 
  generalize dependent e. 
  generalize dependent e'.
  induction t_e; intros; try (inversion H1; fail).
  simpl in H0.
  destruct (String.eqb_spec x x0).
  - symmetry in e0. subst.
    eapply t_record_cons in H0 as [e'' [e_tail' H_eq']]; 
    eauto; subst.
    inversion H; subst. 
    simpl in H1, H2.
    rewrite String.eqb_refl in *.
    inversion H1. inversion H2.
    subst. auto.    
  - assert (H_val := H0).
    eapply t_record_cons in H0 as [e'' [e_tail' H_eq']]; eauto.
    subst.
    inversion H_val; subst.
    inversion H; subst.
    eapply IHt_e2; 
    eauto;
    simpl in *;
    rewrite <- String.eqb_neq in n;
    rewrite String.eqb_sym in n;
    rewrite n in *;
    eauto.
Qed.