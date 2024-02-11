From Coq Require Import Unicode.Utf8.
From Coq Require Import Relation_Definitions.
Require Import Syntax.
Require Import Step.
Require Import Subst.
Require Import Hints.
Require Import Closed.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Lia.
Require Import String.


Reserved Notation "e1 ->>* e2" (at level 70, no associativity) .

Inductive multistep : expr -> expr -> Prop :=
  | multistep_step : 
      ∀ e1 e2, 
      e1 ->> e2 -> 
      e1 ->>* e2 
  | multistep_refl : 
      ∀ e, 
      e ->>* e 
  | multistep_trans :
      ∀ x y z,
      x ->>* y -> 
      y ->>* z -> 
      x ->>* z 
  where "e1 ->>* e2" := (multistep e1 e2)
  .

Hint Constructors multistep : local_hints.

Lemma multistep_step_ : ∀ e1 e2, e1 ->> e2 -> e1 ->>* e2.
Proof.
  eauto with local_hints.
  Show Proof.
Qed.


Example multistep_if :
  <{if 1 == 2 then 3 else 0}> ->>* <{0}>.
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

Example multistep_fix : 
<{
  (fix inner_eq) 1 1
}> ->>* <{true}>.
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
  eapply multistep_trans.
  - apply multistep_step. repeat apply ST_App_Left.
    apply ST_Fix_Fun.
    repeat apply S_Fun_Neq... 
    repeat apply S_If...
  - eapply multistep_trans.
    + apply multistep_step. apply ST_App_Left.
      apply ST_App_Fun;
      try apply S_Fun_Neq;
      repeat apply S_If...
    + eapply multistep_trans.
      * apply multistep_step. apply ST_App_Fun...
        repeat apply S_If...
      * {
      eapply multistep_trans.
      - apply multistep_step. apply ST_If...
      - eapply multistep_trans.  
        + apply multistep_step. apply ST_If_False.
        + eapply multistep_trans.  
          * apply multistep_step. apply ST_If...
          * {
            eapply multistep_trans.
            - apply multistep_step. apply ST_If_False...
            - eapply multistep_trans.
              + apply multistep_step. repeat apply ST_App_Left.
                apply ST_Fix_Fun.
                repeat apply S_Fun_Neq... 
                repeat apply S_If...
              + eapply multistep_trans.
                * apply multistep_step. apply ST_App_Left.
                  apply ST_App_Right...
                * {
                  eapply multistep_trans.
                  - apply multistep_step. apply ST_App_Left.
                    simpl.
                    apply ST_App_Fun...
                    apply S_Fun_Neq...
                    repeat apply S_If...
                  - eapply multistep_trans.
                    + apply multistep_step. apply ST_App_Right...
                    + simpl.
                      eapply multistep_trans.
                      * apply multistep_step. 
                        eapply ST_App_Fun...
                        repeat apply S_If...
                      * {
                      eapply multistep_trans.
                      - apply multistep_step...
                      - eapply multistep_trans... 
                      }
                      
                }
          } 
      

      }
Qed.