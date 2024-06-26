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
  blocking_expr e \/ ∃ e', e --> e'.
Proof with eauto with local_hints.
  intro e.
  pose (
    P (e: expr) :=
      ∀ Σ t,
        has_type Σ empty e t -> 
        blocking_expr e \/ ∃ e', e --> e'
  ).
  pose (
    P0 (branches: lsexpr) :=
      ∀ name_sum Σ t,
        has_type_lsexpr name_sum Σ empty branches t -> 
        value_lsexpr branches \/ ∃ branches', branches -->ₗ branches'
  ).
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0;
  clear P P0;
  try (intros * IH1 * IH2 * IH3 * H_type);
  try (intros * IH1 * IH2 * H_type);
  try (intros * IH * H_type);
  try (intros * H_type);
  try (eauto with local_hints; fail);
  try assert (H_closed := Closed.typed_empty _ _ _ H_type).
  - inversion H_type; inversion H2.

  - inversion H_type; subst.
    apply Closed.closed_app in H_closed 
      as [H_closed_e1 H_closed_e2].
    right.
    assert (H_type_1 := H5).
    assert (H_type_2 := H3).
    apply IH1 in H5 as [H_val_e1 | [e1' H_st_e1]];
    apply IH2 in H3 as [H_val_e2 | [e2' H_st_e2]]...
    apply Canonical_form.t_fun in H_type_1 as [x [e1' H_eq]];
    subst...
    assert (H_subst := Subst.exists_one e1' e2 x H_closed_e2).
    destruct H_subst as [e_subst H_subst]...

  - inversion H_type; subst.
    apply Closed.closed_if in H_closed 
      as [H_closed_e1 [H_closed_e2 H_closed_e3]].
    right.
    assert (H_type_1 := H4).
    assert (H_type_2 := H6).
    assert (H_type_3 := H7).
    apply IH1 in H4 as [H_val_e1 | [e1' H_st_e1]];
    apply IH2 in H6 as [H_val_e2 | [e2' H_st_e2]];
    apply IH3 in H7 as [H_val_e3 | [e3' H_st_e3]]; eauto with local_hints; 
    apply Canonical_form.t_bool in H_type_1 as [H_true | H_false]; subst...

  - inversion H_type; subst.
    apply Closed.closed_let in H_closed.
    right.
    assert (H_type_1 := H5).
    assert (H_type_2 := H6).
    apply IH1 in H5 as [H_val_e1 | [e1' H_st_e1]]...
    assert (H_subst := Subst.exists_one e2 e1  x H_closed).
    destruct H_subst as [e_subst H_subst]...

  - right. 
    inversion H_type; subst.
    apply Closed.closed_minus in H_closed 
      as [H_closed_e1 H_closed_e2].
    assert (H_type_1 := H3).
    assert (H_type_2 := H5).
    apply IH1 in H3 as [H_val_e1 | [e1' H_st_e1]];
    apply IH2 in H5 as [H_val_e2 | [e2' H_st_e2]]...
    apply Canonical_form.t_num in H_type_1 as [z1];
    subst...
    apply Canonical_form.t_num in H_type_2 as [z2];
    subst...

  - right. 
    inversion H_type; subst.
    apply Closed.closed_eq in H_closed 
      as [H_closed_e1 H_closed_e2].
    assert (H_type_1 := H3).
    assert (H_type_2 := H5).
    apply IH1 in H3 as [H_val_e1 | [e1' H_st_e1]];
    apply IH2 in H5 as [H_val_e2 | [e2' H_st_e2]]...
    apply Canonical_form.t_num in H_type_1 as [z1];
    subst...
    apply Canonical_form.t_num in H_type_2 as [z2]...
    destruct (Z.eqb_spec z1 z2); subst...

  - inversion H_type; subst.
    apply Closed.closed_pair in H_closed 
      as [H_closed_e1 H_closed_e2].
    assert (H_type_1 := H3).
    assert (H_type_2 := H5).
    apply IH1 in H3 as [H_val_e1 | [e1' H_st_e1]];
    apply IH2 in H5 as [H_val_e2 | [e2' H_st_e2]]...

  - right. 
    inversion H_type; subst.
    apply Closed.closed_first in H_closed.
    assert (H_type' := H2).
    apply IH in H2 as [H_val_e1 | [e1' H_st_e1]]...
    apply Canonical_form.t_pair in H_type' as [e1 [e2 H_eq]]; subst; inversion H_val_e1...

  - right. 
    inversion H_type; subst.
    apply Closed.closed_second in H_closed.
    assert (H_type' := H2).
    apply IH in H2 as [H_val_e1 | [e1' H_st_e1]]...
    apply Canonical_form.t_pair in H_type' as [e1 [e2 H_eq]]; subst; inversion H_val_e1...
  - inversion H_type; subst.
    apply Closed.closed_record in H_closed 
      as [H_closed_e0 H_closed_tail].
    apply IH1 in H4 as [H_val_e1 | [e1' H_st_e1]];
    apply IH2 in H6 as [H_val_e2 | [e2' H_st_e2]]...

  - right. 
    inversion H_type; subst.
    apply Closed.closed_access in H_closed.
    assert (H_type' := H3).
    apply IH in H3 as [H_val_e1 | [e1' H_st_e1]]...
    Check Canonical_form.record_type_exists.
    eapply Canonical_form.record_type_exists in H5 as [e' H_look]...
  - right. 
    inversion H_type; subst.
    apply Closed.closed_fix in H_closed as H_closed'.
    assert (H_type' := H2).
    apply IH in H2 as [H_val_e1 | [e1' H_st_e1]]...
    eapply Canonical_form.t_fun in H_val_e1 as [x [e' H_eq]]; 
    try rewrite H_eq in *...
    assert (H := Subst.exists_one e' <{ fix fun x : t => e' }> x H_closed).
    destruct H...

  - inversion H_type; subst.
    apply Closed.closed_in_left in H_closed.
    assert (H_type' := H5).
    apply IH in H5 as [H_val_e1 | [e1' H_st_e1]]...

  - inversion H_type; subst.
    apply Closed.closed_in_right in H_closed.
    assert (H_type' := H5).
    apply IH in H5 as [H_val_e1 | [e1' H_st_e1]]...

  - inversion H_type; subst.
    apply Closed.closed_match in H_closed 
      as [H_closed_e [H_closed_eleft H_closed_eright]].
    right.
    assert (H_type_1 := H4).
    assert (H_type_2 := H6).
    assert (H_type_3 := H7).
    apply IH1 in H4 as [H_val_e1 | [e1' H_st_e1]];
    apply IH2 in H6 as [H_val_e2 | [e2' H_st_e2]];
    apply IH3 in H7 as [H_val_e3 | [e3' H_st_e3]]; eauto with local_hints; 
    apply Canonical_form.t_in in H_type_1 as [e' [ H_inl | H_inr]]; subst; inversion H_val_e1...

  - inversion H_type; subst.
    apply Closed.closed_sum_constr in H_closed.
    assert (H_type' := H5).
    apply IH in H5 as [H_val_e1 | [e1' H_st_e1]]...
  - right.
    inversion H_type; subst.
    apply Closed.closed_sum_match in H_closed as [H_closed_e0 H_closed_branches].
    assert (H_type_e0 := H3).
    assert (H_type_branches := H5).
    apply IH1 in H3 as [H_val_e0 | [e1' H_st_e1]]...
    apply IH2 in H5 as [H_val_branches | [branches' H_st_branches]]... admit.
    (* TODO:
        - Définir ST pour quand 2 valeurs
        - Définir forme canonique Sum
        - Finir démo
    
     *)

  - inversion H_type; subst.
    apply IH1 in H8 as [H_v_e0 | [e0' H_st_e0]];
    apply IH2 in H5 as [H_v_l | [l' H_st_l]]...
    
Admitted.


(* 
  intros * H_type.
  assert (H_closed := Closed.typed_empty _ _ _ H_type).
  generalize dependent t.
  induction e; intros;
  try (eauto with local_hints; fail).

  - (* E_Var: Contradiction *) 
    right. inversion H_type; subst. inversion H2.

  - (* E_App: Soit e₁ réduit, soit e₂ réduit, soit AppAbs *)
    right. inversion H_type; subst. 
    apply Closed.closed_app in H_closed as 
      [H_closed_e1 H_closed_e2]. 
    destruct (IHe1 H_closed_e1 (Type_Fun t1 t)) as 
      [H_val_e1 | [e1' H_step_e1] ]...
    destruct (IHe2 H_closed_e2 t1) as 
      [H_val_e2 | [e2' H_step_e2] ]...
    destruct (Canonical_form.t_fun _ _ e1 t1 t H5 H_val_e1) as 
      [x [e' H_eq]]; subst.
    destruct (IHe1 H_closed_e1 _ H5) as 
      [H_val | H_ex].
    + destruct (Subst.exists_one e2 x e') as [e'0 H_sub]...
    + destruct H_ex as [e'0 H_ex]. inversion H_ex.

  - (* E_If: e₁ e₂ ou e₃ réduit *)
    right. inversion H_type; subst. 
    apply Closed.closed_if in H_closed as 
      [H_closed_e1 H_closed_e2]. 
    destruct (IHe1 H_closed_e1 _ H4) as 
      [H_val_e1 | [e' H_step]]...
    eapply Canonical_form.t_bool in H_val_e1...
    destruct H_val_e1 as
        [H_e1_eq | H_e1_eq]; 
    subst...

  - (* E_Let e₁ réduit ou devient e₂[x <- e₁]*)
    right. inversion H_type; subst.
    apply Closed.closed_let in H_closed. 
    destruct (IHe1 H_closed t1) as [H_val_e1 | [e1' H_step_e1] ]...
    destruct (Subst.exists_one e1 x e2) as [e' H_sub]...
  
  - (* E_Minus e₁ ou e₂ réduit ou on soustrait les 2 nombres obtenus *)
    right. inversion H_type; subst.
    apply Closed.closed_minus in H_closed as 
      [H_closed_e1 H_closed_e2].
    apply IHe1 in H3 as He1... apply IHe2 in H5 as He2...
    destruct He1 as [H_v_e1 | [e1' H_step_e1]]...
    destruct He2 as [H_v_e2 | [e2' H_step_e2]]...
    destruct (Canonical_form.t_num _ _ e1 H3 H_v_e1) as [z1 H_z1].
    destruct (Canonical_form.t_num _ _ e2 H5 H_v_e2) as [z2 H_z2].
    subst...
  
  - (* E_Eq: similaire à E_Minus *)
    right. inversion H_type; subst.
    apply Closed.closed_eq in H_closed as 
      [H_closed_e1 H_closed_e2].
    apply IHe1 in H3 as He1... apply IHe2 in H5 as He2...
    destruct He1 as [H_v_e1 | [e1' H_step_e1]]...
    destruct He2 as [H_v_e2 | [e2' H_step_e2]]...
    destruct (Canonical_form.t_num _ _ e1 H3 H_v_e1) as [z1 H_z1].
    destruct (Canonical_form.t_num _ _ e2 H5 H_v_e2) as [z2 H_z2].
    destruct (Z.eqb_spec z1 z2); subst...

  - (* E_Pair: on réduit d'un coté où de l'autre si possible, sinon c'est une valeur *) 
    apply Closed.closed_pair in H_closed 
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
  - (* E_First: on réduit e ou on prend la première composante *)
    inversion H_type; subst.
    assert (
      H := 
      IHe 
      (Closed.closed_first _ H_closed)
      _ 
      H2
    ).
      
    destruct H as [H_val | [e' H_step]].
    + right. 
      apply Canonical_form.t_pair in H2 as [e₁ [e₂ H2]]; 
      subst; inversion H_val; eauto with local_hints. 
    + right. eauto with local_hints.
  - (* E_Second: similaire à E_First *)
    inversion H_type; subst.
    assert (
      H := 
        IHe 
        (Closed.closed_second _ H_closed)
        _ 
        H2
    ).
    destruct H as [H_val | [e' H_step]].
    + right. 
      apply Canonical_form.t_pair in H2 as [e₁ [e₂ H2]]; 
      subst; inversion H_val; eauto with local_hints. 
    + right. eauto with local_hints.
  - (* E_Record_Cons: on réduit tail ou e, ou on a une valeur *)
    inversion H_type; subst.
    apply Closed.closed_record in H_closed 
      as [H_closed_e1 H_closed_e2].
    assert (
      IH1 := 
        IHe1 
        (H_closed_e1)
        _ 
        H4
    ).
    assert (
      IH2 := 
        IHe2 
        (H_closed_e2)
        _ 
        H6
    ).
    destruct IH1 as [H_val_e1 | [e1' H_step_e1]];
    destruct IH2 as [H_val_e2 | [e2' H_step_e2]]; 
    eauto with local_hints.
  - (* E_Record_Access: similaire à E_First et E_Second *)
    inversion H_type; subst.
    assert (
      H := 
        IHe 
        (Closed.closed_access _ _ H_closed)
        _ 
        H3
    ).

    destruct H as [H_val | [e' H_step]].
    + right. 
      eapply Canonical_form.record_type_exists in H5
        as [e' H_look]; eauto with local_hints. 
    + eauto with local_hints.

  - (* E_Fix: On réduit e ou on applique la règle d'évaluation de fix *) 
    right.
    inversion H_type; subst.
    apply Closed.closed_fix in H_closed as H_closed_2.
    destruct (IHe H_closed_2 _ H2) as [H_val | [e' H_step]].
    + apply Canonical_form.t_fun in H2 as [x [e' H_eq]];
      subst; eauto.
      destruct (Subst.exists_one (E_Fix (E_Fun x t e')) x e') as [e'' H_sub]...
    + eexists. apply ST_Fix. apply H_step.
  - (* E_In_Left: on réduit e ou on a une valeur *)
    inversion H_type; subst.
    apply Closed.closed_in_left in H_closed. eapply IHe in H_closed as [H_val_e | [e' H_step_e]]...

  - (* E_In_Right: similaire à E_In_Left *)
    inversion H_type; subst.
    apply Closed.closed_in_right in H_closed. eapply IHe in H_closed as [H_val_e | [e' H_step_e]]...
  - (* E_Match: on réduit e₁ e₂ ou e₃ ou on applique la réduction de match *)
    inversion H_type; subst.
    apply Closed.closed_match in H_closed as [H_closed_e1 [H_closed_e2 H_closed_e3]]. eapply IHe1 in H_closed_e1 as [H_val_e1 | [e1' H_step_e1]]; eapply IHe2 in H_closed_e2 as [H_val_e2 | [e2' H_step_e2]]; eapply IHe3 in H_closed_e3 as [H_val_e3 | [e3' H_step_e3]]...
    right.
    assert (H_v_e1 := H_val_e1).
    eapply Canonical_form.t_in with (t₁ := t₁) (t₂ := t₂) (Γ := empty) in H_v_e1 as [e1' [H_eq_e1 | H_eq_e1]]; subst...
    + exists (E_App e2 e1'). eapply ST_Match_Left_App; 
      inversion H_val_e1...
    + exists (E_App e3 e1'). eapply ST_Match_Right_App; 
      inversion H_val_e1...
  - (* E_Sum_Constr: similaire à E_In_Left *)
    inversion H_type; subst.
    apply Closed.closed_sum_constr in H_closed. eapply IHe in H_closed as [H_val_e | [e' H_step_e]]... *)
  - 
Qed.
Hint Resolve expr_progress : local_hints.
