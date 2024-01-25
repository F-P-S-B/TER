
From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Require Import Maps.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Syntax.
Require Import Subst.
Require Import Step.
Require Import Types.
Require Import Free.
Require Import Progress.
Require Import Hints.


(* Print HintDb local_hints. *)



Theorem preservation : forall e e' t,
  has_type empty e t  ->
  step e e'  ->
  has_type empty e' t.
Proof.
    intros * H_type_e. 
    generalize dependent e'.
    remember empty as Γ.
    induction H_type_e;
    intros e' H_step; try (inversion H_step; subst; eauto with local_hints; fail).
    - inversion H_step; subst; 
      try (apply T_App with t1; eauto).
      + admit.
    - inversion H_step; subst. 
      + eapply T_Let; eauto with local_hints. 
      + eapply subst_typing with (x := x) (t_s:= t1) (e := e2); eauto.
      (* Check closed_empty_type. *)
      (* apply Free.closed_empty_type. *)

Admitted.
 (* - inversion H_step; subst;
      inversion H_type_e2; subst; eauto with local_hints. 
      eapply subst_typing; eauto.
      apply closed_value. assumption.
    - inversion H_step; subst;
      eauto with local_hints.
      eapply subst_typing; eauto. 
      apply closed_value. assumption.
Qed.      *)

Hint Resolve preservation : local_hints.


(* 
  TODO:
    - ajouter arithmétique \/
    - Renforcer `preservation` pour avoir un environnement Γ quelconque \/ 
    - Renforcer `progress` pour avoir un environnement Γ quelconque \/
      Idées: 
        - Ajouter une notion d'expressions closes, de variables libres 


 *)