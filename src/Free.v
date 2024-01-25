From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Require Import Maps.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Syntax.
Require Import Subst.
Require Import Step.
Require Import Types.
Require Import Hints.


Inductive appears_free_in : string -> expr -> Prop :=
  | F_Var : 
      ∀ x, appears_free_in x (E_Var x)
  | F_App_Left : 
      ∀ x (e1 e2 : expr), 
      appears_free_in x e1 -> 
      appears_free_in x (E_App e1 e2)
  | F_App_Right : 
      ∀ x (e1 e2 : expr), 
      appears_free_in x e2 -> 
      appears_free_in x (E_App e1 e2)
  | F_Fun :
      ∀ x y t e, 
      x <> y ->
      appears_free_in x e -> 
      appears_free_in x (E_Fun y t e) 
  | F_If_Cond :
      ∀ x (e1 e2 e3 : expr), 
      appears_free_in x e1 -> 
      appears_free_in x (E_If e1 e2 e3)
  | F_If_Left :
      ∀ x (e1 e2 e3 : expr), 
      appears_free_in x e2 -> 
      appears_free_in x (E_If e1 e2 e3)
  | F_If_Right :
      ∀ x (e1 e2 e3 : expr), 
      appears_free_in x e3 -> 
      appears_free_in x (E_If e1 e2 e3)
  | F_Let_Left :
      ∀ x y e1 e2, 
      appears_free_in x e1 -> 
      appears_free_in x (E_Let y e1 e2) 
  | F_Let_Right :
      ∀ x y e1 e2, 
      x <> y ->
      appears_free_in x e2 -> 
      appears_free_in x (E_Let y e1 e2)
  | F_Minus_Left : 
      ∀ x e1 e2, 
      appears_free_in x e1 -> 
      appears_free_in x (E_Minus e1 e2)
  | F_Minus_Right : 
      ∀ x e1 e2, 
      appears_free_in x e2 -> 
      appears_free_in x (E_Minus e1 e2)
. 

Hint Constructors appears_free_in : local_hints.

Local Lemma not_free_var_neq : forall x y, ~ appears_free_in y (E_Var x) -> y <> x.
Proof.
  intros x y H_not_free H_eq_contra.
  apply H_not_free.
  subst. apply F_Var.
Qed.  


Local Lemma neq_var_not_free : forall x y,
y <> x -> ~ appears_free_in y (E_Var x).
Proof.
  intros x y  H_neq H_free_contra.
  inversion H_free_contra; subst. 
  contradiction.
Qed.  

Local Lemma not_free_fun : 
  forall x y e t, ~ appears_free_in y (E_Fun x t e) -> x <> y -> ~ appears_free_in y e.
Proof. 
  intros * H_not_free H_neq H_contra.
  apply H_not_free.
  apply F_Fun; eauto.
Qed.

Local Lemma not_free_let_left : 
  forall x y e1 e2, ~ appears_free_in y (E_Let x e1 e2) -> ~ appears_free_in y e1.
Proof. 
  intros * H_not_free H_contra.
  apply H_not_free.
  apply F_Let_Left; eauto.
Qed.


Local Lemma not_free_let_right : 
  forall x y e1 e2, ~ appears_free_in y (E_Let x e1 e2) -> x <> y -> ~ appears_free_in y e2.
Proof. 
  intros * H_not_free H_neq H_contra.
  apply H_not_free.
  apply F_Let_Right; eauto.
Qed.

  

Local Lemma no_impact : forall Γ (e : expr) t y t', 
  ~ appears_free_in y e -> 
  has_type (y |-> t'; Γ) e t ->
  has_type Γ e t.
Proof.
  intros * H_not_free H_type.
  remember (y |-> t'; Γ) as Γ'.
  generalize dependent Γ.
  induction H_type; intros; subst; eauto with local_hints.
  - apply not_free_var_neq in H_not_free. rewrite update_neq in H; auto.
    apply T_Var; auto.
  - apply T_Fun.
    destruct (String.eqb_spec x y).
    + subst. rewrite update_shadow in H_type. assumption.
    + apply not_free_fun in H_not_free; auto.
      apply IHH_type; auto. rewrite update_permute; auto.
  - apply T_App with t1; eauto with local_hints.
  - apply T_If; eauto with local_hints.
  - eapply T_Let; eauto with local_hints.
    destruct (String.eqb_spec x y).
    + subst. rewrite update_shadow in H_type2. assumption.
    + apply not_free_let_right in H_not_free; auto.
      apply IHH_type2; auto. rewrite update_permute; auto.
  - eapply T_Minus; eauto with local_hints. 
Qed.

Hint Resolve no_impact : local_hints.


Definition well_typed (e : expr) t := ∃ Γ, has_type Γ e t.

Definition closed (e : expr) :=
  ∀ x, ~ appears_free_in x e.

Lemma closed_typed_empty : ∀ e t, 
  closed e ->
  well_typed e t ->
  has_type empty e t.  
Proof.
  intros e t H_closed [Γ H_type].
  unfold closed in *.
  induction H_type; eauto with local_hints.
  - specialize H_closed with x. exfalso. apply H_closed.
    apply F_Var.
  - induction Γ; auto with local_hints.
    apply IHΓ.
    destruct (String.eqb_spec x key).
    + subst. rewrite update_shadow in H_type. assumption.
    + rewrite update_permute in H_type; auto.
      apply no_impact with key val; auto. 
      specialize H_closed with key.
      apply not_free_fun in H_closed; auto.
  - apply T_App with t1; 
    [ apply IHH_type1 | apply IHH_type2];
    intros x H_contra;
    specialize H_closed with x; 
    eauto with local_hints.
  - apply T_If;
    [ apply IHH_type1 | apply IHH_type2 | apply IHH_type3 ]; intros x H_contra;
    specialize H_closed with x; 
    eauto with local_hints.
  - induction Γ.
    + eapply T_Let; eauto.
    + apply IHΓ.
      * apply no_impact in H_type1; eauto.
        eapply not_free_let_left in H_closed.
        eapply H_closed.
      * destruct (String.eqb_spec x key).
      {
        subst. rewrite update_shadow in *. assumption.
      }
      {
        eapply not_free_let_right in H_closed; 
        eauto.
        rewrite update_permute in H_type2.
        apply no_impact in H_type2; eauto.
        symmetry. exact n.        
      }
  - apply T_Minus;
    [ apply IHH_type1 | apply IHH_type2];
    intros x H_contra;
    specialize H_closed with x; 
    eauto with local_hints.
Qed.


Lemma subst_typing : ∀ Γ s x e e' t_e t_s, 
    has_type (x |-> t_s; Γ) e t_e ->
    (* has_type empty s t_s ->  (* Dans le cas où on n'a pas de termes clos*) *)
    closed s -> 
    has_type Γ s t_s ->
    substitution s x e e' -> 
    has_type Γ e' t_e.
Proof.
    intros * H_type_e H_closed H_type_s H_subst.
    generalize dependent t_e.
    generalize dependent t_s.
    generalize dependent Γ.
    induction H_subst; intros;
    try (inversion H_type_e; subst; eauto with local_hints; fail).
    - inversion H_type_e; subst. 
      rewrite Maps.update_eq in H1. inversion H1; subst.
      assumption.
    - inversion H_type_e; subst. 
      apply T_Var. rewrite update_neq in H2; auto.
    - inversion H_type_e; subst.
      apply T_Fun.   
      rewrite Maps.update_shadow in H4. assumption.    
    - inversion H_type_e; subst.
      apply T_Fun.
      rewrite Maps.update_permute in H5; auto.
      eapply IHH_subst; eauto.
      apply weakening_empty.
      apply closed_typed_empty with (t := t_s) in H_closed;
      unfold well_typed; eauto.

    - inversion H_type_e; subst. eapply T_Let; eauto.
      rewrite Maps.update_shadow in H5. auto.
    - inversion H_type_e; subst. eapply T_Let; eauto.
      rewrite Maps.update_permute in H6; auto.
      eapply IHH_subst2; eauto.
      apply weakening_empty.
      apply closed_typed_empty with (t := t_s) in H_closed;
      unfold well_typed; eauto.
Qed.     

Hint Resolve subst_typing : local_hints.


Local Lemma is_in_context :
  forall Γ y e t, 
  appears_free_in y e -> 
  has_type Γ e t -> 
  exists v, Γ ? y = Some v.
Proof.
  intros * H_free H_type.
  generalize dependent Γ. 
  generalize dependent t. 
  induction H_free; subst; intros; try (inversion H_type; eauto with local_hints; fail). 
  - inversion H_type; subst. rewrite <- update_neq with (x2 := y) (v := t); eauto.
  - inversion H_type; subst. rewrite <- update_neq with (x2 := y) (v := t1); eauto.
Qed.
  

Lemma closed_empty_type : 
  forall e t, has_type empty e t -> closed e.
Proof.
  intros * H_type y H_contra.
  assert (H:= is_in_context _ _ _ _ H_contra H_type).
  destruct H. inversion H.
Qed.