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
    has_type empty e t -> 
    value e \/ ∃ e', step e e'.
Proof with eauto with local_hints.
    intros * H_type.
    assert (H_closed := Closed.typed_empty _ _ H_type).
    generalize dependent t.
    induction e; intros;
    try (eauto with local_hints; fail);
    (right; inversion H_type; subst)...

    - inversion H1.

    - apply Closed.closed_app in H_closed as 
        [H_closed_e1 H_closed_e2]. 
      destruct (IHe1 H_closed_e1 (Type_Fun t1 t)) as 
        [H_val_e1 | [e1' H_step_e1] ]...
      destruct (IHe2 H_closed_e2 t1) as 
        [H_val_e2 | [e2' H_step_e2] ]...
      destruct (Canonical_form.t_fun e1 t1 t H4 H_val_e1) as 
        [x [e' H_eq]]; subst.
      destruct (IHe1 H_closed_e1 _ H4) as 
        [H_val | H_ex].
      + destruct (Subst.exists_one e2 x e') as [e'0 H_sub]...
      + destruct H_ex as [e'0 H_ex]...

    - apply Closed.closed_if in H_closed as 
        [H_closed_e1 H_closed_e2]. 
      destruct (IHe1 H_closed_e1 _ H3) as 
        [H_val_e1 | [e' H_step]]...
      apply Canonical_form.t_bool in H_val_e1...
      destruct H_val_e1 as
         [H_e1_eq | H_e1_eq]; 
      subst...

    - apply Closed.closed_let in H_closed. 
      destruct (IHe1 H_closed t1) as [H_val_e1 | [e1' H_step_e1] ]...
      destruct (Subst.exists_one e1 x e2) as [e' H_sub]...
    
    - apply Closed.closed_minus in H_closed as 
        [H_closed_e1 H_closed_e2].
      apply IHe1 in H2 as He1... apply IHe2 in H4 as He2...
      destruct He1 as [H_v_e1 | [e1' H_step_e1]]...
      destruct He2 as [H_v_e2 | [e2' H_step_e2]]...
      destruct (Canonical_form.t_num e1 H2 H_v_e1) as [z1 H_z1].
      destruct (Canonical_form.t_num e2 H4 H_v_e2) as [z2 H_z2].
      subst...
      
Qed.

Hint Resolve expr_progress : local_hints.
