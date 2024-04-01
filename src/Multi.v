From Coq Require Import Unicode.Utf8.
Require Import Syntax.
Require Import Step.
Require Import Subst.
Require Import Hints.
Require Import Closed.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Lia.
Require Import String.


Reserved Notation "e₁ -->* e₂" (at level 70, no associativity) .

Inductive multistep : expr -> expr -> Prop :=
  | multistep_refl : 
      ∀ e, 
      e -->* e 
  | multistep_step : 
      ∀ e₁ e₂, 
      e₁ --> e₂ -> 
      e₁ -->* e₂ 
  | multistep_trans :
      ∀ x y z,
      x -->* y -> 
      y -->* z -> 
      x -->* z 
  where "e₁ -->* e₂" := (multistep e₁ e₂)
. 
Check multistep_ind.

(* 
  TODO: Prouver équivalence avec une définition algorithmique + définir Induction par la gauche et la droite
*)

Hint Constructors multistep : local_hints.

Example multistep_if :
  <{if 1 == 2 then 3 else 0}> -->* <{0}>.
Proof.
  eauto 6 with zarith local_hints.
Qed.

Definition eq := "eq"%string.
Definition m := "m"%string.
Definition n := "n"%string.

Definition inner_eq := <{
  fun eq : (Type_Num -> Type_Num -> Type_Bool) =>
    fun m : Type_Num => 
      fun n : Type_Num => 
        if m == 0 
        then n == 0 
        else 
          if n == 0 
          then false 
          else  
            eq (n-1) (m-1)
}>.


Goal <{(fix inner_eq) 1 1}> -->* <{true}>.
Proof with eauto 8 with zarith local_hints.
  assert (H_closed_fun_eq : 
    closed (E_Fix inner_eq)
  ).
  {
    unfold inner_eq.
    intros x H_n.
      inversion H_n.
      inversion H0.
      inversion H5; subst.
      inversion H10; subst.
      inversion H6; subst;
      try (
        inversion H1; subst;
        inversion H4; subst; eauto; fail
      ).
      inversion H1; subst; inversion H4; subst; inversion H7; subst; eauto; inversion H9; subst; eauto; inversion H11; subst; eauto.
  }
  assert (eq <> n). {
    intro; inversion H.
  }
  assert (eq <> m). {
    intro; inversion H0.
  }
  assert (n <> m). {
    intro; inversion H1.
  }
  assert (closed 1). {
    intros x Hc; inversion Hc.
  }
  assert (closed 0). {
    intros x Hc; inversion Hc.
  }
  eapply multistep_trans; 
  eapply multistep_trans; 
  eapply multistep_trans;
  eapply multistep_trans.
  - apply multistep_step. 
    repeat apply ST_App_Left.
    apply ST_Fix_Fun.
    repeat apply S_Fun_Neq... 
    repeat apply S_If...
  - apply multistep_step. apply ST_App_Left. 
    apply ST_App_Fun;
    try apply S_Fun_Neq;
    try repeat apply S_If...
  - apply multistep_step... 
    apply ST_App_Fun;
    try apply S_Fun_Neq;
    try repeat apply S_If...
  - apply multistep_step...
  - apply multistep_step...
  - apply multistep_step...
  - apply multistep_step...
  - apply multistep_step.
    repeat apply ST_App_Left.
    apply ST_Fix_Fun.
    repeat apply S_Fun_Neq;
    repeat apply S_If...
  - apply multistep_step...
  - apply multistep_step. simpl.
    apply ST_App_Left.
    apply ST_App_Fun;
    try apply S_Fun_Neq;
    repeat apply S_If...
  - apply multistep_step...
  - apply multistep_step. simpl.
    apply ST_App_Fun;
    repeat apply S_If...
  - apply multistep_step...
  - apply multistep_step...
  - apply multistep_step...  
  - apply multistep_refl. 
Qed.

Check multistep_ind. 


(* TODO:
    prouver que x --> y -> P x y -> x -->* y -> P x y ou similaire
 *)
Lemma exists_red : ∀ x y, x -->* y -> x = y \/ ∃ aux, x --> aux /\ aux -->* y.
Proof with eauto with local_hints.
  intros.
  induction H...
  destruct IHmultistep1 as [ H_x_eq_y | [x_aux [H_x_red H_xaux_red]]];
  destruct IHmultistep2 as [ H_y_eq_z | [y_aux [H_y_red H_yaux_red]]]; subst...
Qed.

Hint Resolve exists_red : local_hints.

Theorem multistep_step_multistep :
  ∀ x y z, x --> y -> y -->* z -> x -->* z.
Proof with eauto with local_hints.
  intros.
  apply multistep_trans with y...
Qed.

Check multistep_ind.


Theorem multistep_ind_left (P : expr -> expr -> Prop) :
  (∀ e : expr, P e e) → 
  (∀ x y z : expr, x --> y → y -->* z → P y z → P x z) → 
  ∀ e e' : expr, e -->* e' → P e e'.
Proof with eauto with local_hints.
Admitted.
