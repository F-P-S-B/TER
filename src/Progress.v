From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Hints.
Require Import Syntax.
Require Import Types.
Require Import Subst.
Require Import Step.
Require Import Canonical_form.
Require Maps.
Import Maps.Notations.

Theorem expr_progress : ∀ e Σ t,
  has_type Σ empty e t -> 
  value e \/ ∃ e', e --> e'.
Proof with eauto with local_hints.
  intro e.
  pose (
    P (e: expr) :=
      ∀ Σ t,
        Σ / empty |- e : t -> 
        value e \/ ∃ e', e --> e'
  ).
  pose (
    P0 (lse : lsexpr) :=
      ∀ Σ, 
      (
        ∀ name_sum t, 
        Σ / empty |-ₛ name_sum ~> lse : t -> 
        value_lsexpr lse \/ ∃ lse', lse -->ₗ lse'
      ) /\
      (
        ∀ t, 
        Σ / empty |-ᵣ lse : t -> 
        value_lsexpr lse \/ ∃ lse', lse -->ₗ lse'
      ) 
  ).
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0;
  clear e P P0...

  - intros * H_type. inversion H_type; subst. inversion H2.

  - intros * IH1 * IH2 * H_type. right.
    inversion H_type; subst...
    apply IH1 in H5 as [H_val_e1 | [e1' H_step_e1]];
    apply IH2 in H3 as [H_val_e2 | [e2' H_step_e2]]...
    inversion H_type; subst.
    apply Canonical_form.t_fun in H5 as [x [e1' H_eq]]; subst...
    apply Closed.typed_empty in H3.
    apply (Subst.exists_one e1' e2 x) in H3 as [eₛ H_subst]...
  
  - intros * IH1 * IH2 * IH3 * H_type. right.
    inversion H_type; subst.
    assert (H_type_e1 := H4).
    apply IH1 in H4 as [H_val_e1 | [e1' H_step_e1]]...
    apply Canonical_form.t_bool in H_type_e1 as [H | H]; subst...
    
  - intros * IH1 * IH2 * H_type. right.
    inversion H_type; subst.
    assert (H_type_e1 := H5).
    apply IH1 in H5 as [H_val_e1 | [e1' H_step_e1]]...
    apply Closed.typed_empty in H_type_e1.
    apply (Subst.exists_one e2 e1 x) in H_type_e1 as [eₛ H_subst]...

  - intros * IH1 * IH2 * H_type. right.
    inversion H_type; subst.
    assert (H_type_e1 := H3).
    assert (H_type_e2 := H5).
    apply IH1 in H3 as [H_val_e1 | [e1' H_step_e1]]...
    apply IH2 in H5 as [H_val_e2 | [e2' H_step_e2]]...
    apply Canonical_form.t_num in H_type_e1 as [z₁ H_eq_e1]...
    apply Canonical_form.t_num in H_type_e2 as [z₂ H_eq_e2]; subst...

  - intros * IH1 * IH2 * H_type. right.
    inversion H_type; subst.
    assert (H_type_e1 := H3).
    assert (H_type_e2 := H5).
    apply IH1 in H3 as [H_val_e1 | [e1' H_step_e1]]...
    apply IH2 in H5 as [H_val_e2 | [e2' H_step_e2]]...
    apply Canonical_form.t_num in H_type_e1 as [z₁ H_eq_e1]...
    apply Canonical_form.t_num in H_type_e2 as [z₂ H_eq_e2]; subst...
    destruct (Z.eqb_spec z₁ z₂); subst...

  - intros * IH1 * IH2 * H_type.
    inversion H_type; subst.
    assert (H_type_e1 := H3).
    assert (H_type_e2 := H5).
    apply IH1 in H3 as [H_val_e1 | [e1' H_step_e1]]...
    apply IH2 in H5 as [H_val_e2 | [e2' H_step_e2]]...

  - intros * IH1 * H_type. right.
    inversion H_type; subst.
    assert (H_type_e := H2).
    apply IH1 in H2 as [H_val_e | [e' H_step_e]]...
    apply Canonical_form.t_pair in H_type_e as [e₁ [e₂ H_eq]]; 
    subst... inversion H_val_e...

  - intros * IH1 * H_type. right.
    inversion H_type; subst.
    assert (H_type_e := H2).
    apply IH1 in H2 as [H_val_e | [e' H_step_e]]...
    apply Canonical_form.t_pair in H_type_e as [e₁ [e₂ H_eq]]; 
    subst... inversion H_val_e...

  - intros * IH1 * H_type. 
    inversion H_type; subst.
    apply IH1 in H2 as [H_val_rec | [rec' H_step_rec]]...

  - intros * IH1 * H_type. right.
    inversion H_type; subst.
    assert (H_type_e := H3).
    apply IH1 in H3 as [H_val_e | [e' H_step_e]]...
    apply Canonical_form.t_record in H_type_e as [rec [H_eq H_type_rec]]; subst...
    eapply Canonical_form.record_type_lookup in H5 as [e' H_lookup]...
    inversion H_val_e...

  - intros * IH1 * H_type. right.
    inversion H_type; subst.
    assert (H_type_e := H2).
    apply IH1 in H2 as [H_val_e | [e' H_step_e]]...
    apply Canonical_form.t_fun in H_type_e as [x [e1' H_eq]]; subst...
    inversion H_type; subst.
    apply Closed.typed_empty in H_type.
    eapply (Subst.exists_one _ _ _) in H_type as [eₛ H_subst]...

  - intros * IH1 * H_type.
    inversion H_type; subst.
    assert (H_type_e := H5).
    apply IH1 in H5 as [H_val_e1 | [e1' H_step_e1]]...

  - intros * IH1 * H_type.
    inversion H_type; subst.
    assert (H_type_e := H5).
    apply IH1 in H5 as [H_val_e1 | [e1' H_step_e1]]...

  - intros * IH1 * IH2 * IH3 * H_type. right.
    inversion H_type; subst.
    assert (H_type_e1 := H4).
    apply IH1 in H4 as [H_val_e1 | [e1' H_step_e1]]...
    apply IH2 in H6 as [H_val_e2 | [e2' H_step_e2]]...
    apply IH3 in H7 as [H_val_e3 | [e3' H_step_e3]]...
    apply Canonical_form.t_in in H_type_e1 as [e' [H_eq | H_eq]]; subst;
    inversion H_val_e1; subst...

  - intros * IH1 * H_type.
    inversion H_type; subst.
    assert (H_type_e := H5).
    apply IH1 in H5 as [H_val_e | [e' H_step_e]]...

  - intros * IH1 * IH2 * IH3 * H_type. right.
    inversion H_type; subst.
    assert (H_type_e0 := H4).
    assert (H_type_branches := H7).
    assert (H_type_default := H6).
    apply IH1 in H4 as [H_val_e0 | [e0' H_step_e0]]...
    apply IH3 in H7 as [H_val_branches | [branches' H_step_branches]]...
    apply IH2 in H6 as [H_val_default | [default' H_step_default]]...
    apply Canonical_form.t_enum 
      in H_type_e0 
      as [ constr [e0' [ t0 [ H_lookup [ H_type_e0' H_eq ]]]]]; subst...
    pose (
      res := lookup_lsexpr constr branches
    ).
    inversion H_val_e0; subst.
    destruct res eqn:H_res...

  - intros * IH1 * IH2 *.
    split; intros * H_type.
    + inversion H_type; subst.
      assert (H_type_e0 := H8).
      assert (H_type_l := H5).
      apply IH1 in H8 as [H_val_e0 | [e0' H_step_e0]]...
      apply IH2 in H5 as [H_val_l | [lse' H_step_l]]...
    + inversion H_type; subst.
      assert (H_type_e0 := H6).
      assert (H_type_l := H5).
      apply IH1 in H6 as [H_val_e0 | [e0' H_step_e0]]...
      apply IH2 in H5 as [H_val_l | [lse' H_step_l]]...
Qed.
