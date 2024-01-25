From Coq Require Import Unicode.Utf8.
Require Import ZArith.
Local Open Scope Z_scope.
Require Import Syntax.
Require Import Types.
Require Import Hints.

Local Lemma t_num : ∀ e,
    has_type empty e Type_Num -> 
    value e ->
    ∃ z, e = E_Num z.
Proof.
    intros * H_type H_val.
    inversion H_val; eauto; 
    subst; inversion H_type.
Qed.

Hint Resolve t_num : local_hints.

Local Lemma t_bool : ∀ e,
    has_type empty e Type_Bool -> 
    value e ->
    e = E_True \/ e = E_False.
Proof.
    intros * H_type H_val.
    inversion H_val; subst; auto;
    inversion H_type.
Qed.

Hint Resolve t_bool : local_hints.

Local Lemma t_fun : ∀ e t1 t2,
    has_type empty e (Type_Fun t1 t2) -> 
    value e ->
    ∃ x e', e = E_Fun x t1 e'. 
Proof.
    intros * H_type H_val.
    inversion H_val; subst; try (inversion H_type; fail).
    inversion H_type; subst.
    eauto.
Qed.
Hint Resolve t_fun : local_hints.
