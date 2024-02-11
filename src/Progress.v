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




Theorem expr_progress : ∀ e t,
  empty ⊢ e ∈ t -> 
  value e \/ ∃ e', e ->> e'.
Proof with eauto with local_hints.
  intros * H_type.
  assert (H_closed := Closed.typed_empty _ _ H_type).
  generalize dependent t.
  induction e; intros;
  try (eauto with local_hints; fail).

  - right. inversion H_type; subst. inversion H1.

  - right. inversion H_type; subst. 
    apply Closed.closed_app in H_closed as 
      [H_closed_e1 H_closed_e2]. 
    destruct (IHe1 H_closed_e1 (Type_Fun t1 t)) as 
      [H_val_e1 | [e1' H_step_e1] ]...
    destruct (IHe2 H_closed_e2 t1) as 
      [H_val_e2 | [e2' H_step_e2] ]...
    destruct (Canonical_form.t_fun _ e1 t1 t H4 H_val_e1) as 
      [x [e' H_eq]]; subst.
    destruct (IHe1 H_closed_e1 _ H4) as 
      [H_val | H_ex].
    + destruct (Subst.exists_one e2 x e') as [e'0 H_sub]...
    + destruct H_ex as [e'0 H_ex]...

  - right. inversion H_type; subst. 
    apply Closed.closed_if in H_closed as 
      [H_closed_e1 H_closed_e2]. 
    destruct (IHe1 H_closed_e1 _ H3) as 
      [H_val_e1 | [e' H_step]]...
    eapply Canonical_form.t_bool in H_val_e1...
    destruct H_val_e1 as
        [H_e1_eq | H_e1_eq]; 
    subst...

  - right. inversion H_type; subst.
    apply Closed.closed_let in H_closed. 
    destruct (IHe1 H_closed t1) as [H_val_e1 | [e1' H_step_e1] ]...
    destruct (Subst.exists_one e1 x e2) as [e' H_sub]...
  
  - right. inversion H_type; subst.
    apply Closed.closed_minus in H_closed as 
      [H_closed_e1 H_closed_e2].
    apply IHe1 in H2 as He1... apply IHe2 in H4 as He2...
    destruct He1 as [H_v_e1 | [e1' H_step_e1]]...
    destruct He2 as [H_v_e2 | [e2' H_step_e2]]...
    destruct (Canonical_form.t_num _ e1 H2 H_v_e1) as [z1 H_z1].
    destruct (Canonical_form.t_num _ e2 H4 H_v_e2) as [z2 H_z2].
    subst...
  
  - right. inversion H_type; subst.
    apply Closed.closed_eq in H_closed as 
      [H_closed_e1 H_closed_e2].
    apply IHe1 in H2 as He1... apply IHe2 in H4 as He2...
    destruct He1 as [H_v_e1 | [e1' H_step_e1]]...
    destruct He2 as [H_v_e2 | [e2' H_step_e2]]...
    destruct (Canonical_form.t_num _ e1 H2 H_v_e1) as [z1 H_z1].
    destruct (Canonical_form.t_num _ e2 H4 H_v_e2) as [z2 H_z2].
    destruct (Z.eqb_spec z1 z2); subst...

  - apply Closed.closed_pair in H_closed 
      as [H_closed_e1 H_closed_e2]. 
    inversion H_type; subst.
    eapply IHe1 in H_closed_e1 
      as [H_val_e1 | [e1' H_step_e1]];
    eauto;
    eapply IHe2 in H_closed_e2 
      as [H_val_e2 | [e2' H_step_e2]];
    eauto; 
      try (right; eexists; eauto with local_hints; fail).
    + left. apply V_Pair; auto.
  - inversion H_type; subst.
    assert (
      H := 
      IHe 
      (Closed.closed_first _ H_closed)
      _ 
      H1
    ).
      
    destruct H as [H_val | [e' H_step]].
    + right. 
      apply Canonical_form.t_pair in H1 as [e₁ [e₂ H1]]; 
      subst; inversion H_val; eauto with local_hints. 
    + right. eauto with local_hints.
  - inversion H_type; subst.
    assert (
      H := 
        IHe 
        (Closed.closed_second _ H_closed)
        _ 
        H1
    ).
    destruct H as [H_val | [e' H_step]].
    + right. 
      apply Canonical_form.t_pair in H1 as [e₁ [e₂ H1]]; 
      subst; inversion H_val; eauto with local_hints. 
    + right. eauto with local_hints.
  - inversion H_type; subst.
    apply Closed.closed_record in H_closed 
      as [H_closed_e1 H_closed_e2].
    assert (
      IH1 := 
        IHe1 
        (H_closed_e1)
        _ 
        H3
    ).
    assert (
      IH2 := 
        IHe2 
        (H_closed_e2)
        _ 
        H5
    ).
    destruct IH1 as [H_val_e1 | [e1' H_step_e1]];
    destruct IH2 as [H_val_e2 | [e2' H_step_e2]]; 
    eauto with local_hints.
  - inversion H_type; subst.
    assert (
      H := 
        IHe 
        (Closed.closed_access _ _ H_closed)
        _ 
        H2
    ).

    destruct H as [H_val | [e' H_step]].
    + right. 
      eapply Canonical_form.record_type_exists in H4 
        as [e' H_look]; eauto with local_hints. 
    + eauto with local_hints.

  - right.
    inversion H_type; subst.
    apply Closed.closed_fix in H_closed as H_closed_2.
    destruct (IHe H_closed_2 _ H1) as [H_val | [e' H_step]].
    + apply Canonical_form.t_fun in H1 as [x [e' H_eq]];
      subst; eauto.
      destruct (Subst.exists_one (E_Fix (E_Fun x t e')) x e') as [e'' H_sub]...
    + eexists. apply ST_Fix. apply H_step.
Qed.      

Hint Resolve expr_progress : local_hints.
