From Coq Require Import Unicode.Utf8.
Require Maps.
Import Maps.Notations.
Require Import Syntax.
Require Import Step.
Require Import Subst.
Require Import Hints.
Require Import Closed.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Lia.
Require Import String.
Require Import List.
Import ListNotations.



Inductive pair_free : expr -> Prop :=
  | PF_Var : 
      ∀ (x : string), pair_free <{x}>
  | PF_App : 
      ∀ (e₁ e₂ : expr),
      pair_free e₁ -> 
      pair_free e₂ -> 
      pair_free <{e₁ e₂}>
  | PF_Fun :
      ∀ x t e,
      pair_free e -> 
      pair_free <{fun x : t => e}>
  | PF_True :
    pair_free <{true}>
  | PF_False :
    pair_free <{false}>
  | PF_If : 
      ∀ (e₁ e₂ e₃ : expr),
      pair_free e₁ -> 
      pair_free e₂ -> 
      pair_free e₃ -> 
      pair_free <{if e₁ then e₂ else e₃}>
  | PF_Let :
      ∀ x (e₁ e₂ : expr),
      pair_free e₁ -> 
      pair_free e₂ -> 
      pair_free <{let x = e₁ in e₂}>
  | PF_Num :
      ∀ (z : Z), 
      pair_free <{z}>
  | PF_Minus : 
      ∀ (e₁ e₂ : expr),
      pair_free e₁ -> 
      pair_free e₂ -> 
      pair_free <{e₁ - e₂}>
  | PF_Eq :
      ∀ (e₁ e₂ : expr),
      pair_free e₁ -> 
      pair_free e₂ -> 
      pair_free <{e₁ == e₂}>
  | PF_Record_Nil :
      pair_free <{nil}>
  | PF_Record_Cons :
      ∀ x e tail, 
      pair_free tail -> 
      pair_free e -> 
      pair_free <{ x := e ; tail }>
  | PF_Record_Access :
      ∀ e x,
      pair_free e -> 
      pair_free <{e :: x}>
  | PF_Fix :
      ∀ e, 
      pair_free e -> 
      pair_free <{fix e}>
  | PF_In_Left :
      ∀ t₁ t₂ e, 
      pair_free e -> 
      pair_free (E_In_Left t₁ t₂ e)
  | PF_In_Right :
      ∀ t₁ t₂ e, 
      pair_free e -> 
      pair_free (E_In_Right t₁ t₂ e)
  | PF_Match :
      ∀ e e_left e_right, 
      pair_free e -> 
      pair_free e_left -> 
      pair_free e_right -> 
      pair_free (E_Match e e_left e_right)
  | PF_Unit : pair_free E_Unit
  | PF_Enum_Constr : 
      ∀ constr e,
      pair_free e -> 
      pair_free (E_Sum_Constr constr e)
.


Fixpoint to_pair_free_type (t : type) :=
  match t with
  | Type_Num => Type_Num
  | Type_Bool => Type_Bool
  | Type_Fun t₁ t₂ => Type_Fun (to_pair_free_type t₁) (to_pair_free_type t₂)
  | Type_Prod t₁ t₂ => 
    Type_Record_Cons 
      "first"%string (to_pair_free_type t₁) 
      (Type_Record_Cons 
        "second"%string (to_pair_free_type t₂)
        Type_Record_Nil)
  | Type_Record_Nil => Type_Record_Nil
  | Type_Record_Cons x t₁ t₂ => Type_Record_Cons x (to_pair_free_type t₁) (to_pair_free_type t₂)
  | Type_Disjoint_Union t₁ t₂ => Type_Disjoint_Union (to_pair_free_type t₁) (to_pair_free_type t₂)
  | Type_Unit => Type_Unit
  | Type_Sum name => Type_Sum name
  end.

Fixpoint to_pair_free (e : expr) : expr :=
  match e with 
  | E_Var x => <{x}>
  | <{e₁ e₂}> => 
      let e₁ := to_pair_free e₁ in
      let e₂ := to_pair_free e₂ in
      <{e₁ e₂}>
  | <{fun x : t => e}> => 
    let e := to_pair_free e in
    let t := to_pair_free_type t in
    <{fun x : t => e}>
  | E_True => E_True
  | E_False => E_False
  | <{ if e₁ then e₂ else e₃}> => 
      let e₁ := to_pair_free e₁ in
      let e₂ := to_pair_free e₂ in
      let e₃ := to_pair_free e₃ in
      <{if e₁ then e₂ else e₃}>
  | <{let x = e₁ in e₂}> => 
      let e₁ := to_pair_free e₁ in
      let e₂ := to_pair_free e₂ in
      <{let x = e₁ in e₂}>
  | E_Num z => E_Num z
  | <{e₁ - e₂}> => 
      let e₁ := to_pair_free e₁ in
      let e₂ := to_pair_free e₂ in
      <{e₁ - e₂}>
  | <{e₁ == e₂}> => 
    let e₁ := to_pair_free e₁ in
    let e₂ := to_pair_free e₂ in
    <{e₁ == e₂}>
  | <{ (e₁, e₂) }> => 
      let e₁ := to_pair_free e₁ in
      let e₂ := to_pair_free e₂ in
      let fst := "first"%string in
      let snd := "second"%string in
      <{fst := e₁ ; snd := e₂ ; nil}>
  | <{ first e }> => 
      let e := to_pair_free e in
      let fst := "first"%string in
      <{e :: fst}>
  | <{ second e }> => 
      let e := to_pair_free e in
      let snd := "second"%string in
      <{e :: snd}>
  | <{nil}> => <{nil}>
  | <{x := e; tail}> => 
      let e := to_pair_free e in 
      let tail := to_pair_free tail in 
      <{x := e; tail}>
  | <{e :: x}> => 
      let e := to_pair_free e in 
      <{e :: x}>
  | <{fix e}> => 
      let e := to_pair_free e in 
      <{fix e}>
  | E_In_Left t₁ t₂ e => 
      E_In_Left 
        (to_pair_free_type t₁) 
        (to_pair_free_type t₂)
        (to_pair_free e)
  | E_In_Right t₁ t₂ e => 
      E_In_Right 
        (to_pair_free_type t₁) 
        (to_pair_free_type t₂)
        (to_pair_free e)

  | E_Match e e_left e_right => 
      E_Match 
        (to_pair_free e)
        (to_pair_free e_left)
        (to_pair_free e_right)
  | E_Unit => E_Unit
  | E_Sum_Constr constr e => E_Sum_Constr constr (to_pair_free e)
  end.

Hint Constructors pair_free : local_hints.
Definition t_pair_bool := Type_Prod Type_Num Type_Bool.

Compute (to_pair_free <{ first (second x , first y)}>).

Lemma to_pair_free_is_pair_free :
  ∀ e,
  pair_free (to_pair_free e).
Proof.
  intro.
  induction e; eauto with local_hints. 
Qed.

Hint Resolve to_pair_free_is_pair_free : local_hints.

Lemma to_pair_free_free:
  ∀ xf e, 
  is_free_in xf (to_pair_free e) -> 
  is_free_in xf e.
Proof. 
  intros.
  induction e; try (inversion H; subst; eauto with local_hints).
  inversion H1; subst; eauto with local_hints. inversion H2.
Qed.

Hint Resolve to_pair_free_free : local_hints.


Lemma to_pair_free_value:
  ∀ e, 
  value e -> 
  value (to_pair_free e).
Proof. 
  intros.
  induction e; try (inversion H; subst; eauto with local_hints).
Qed.

Hint Resolve to_pair_free_value : local_hints.

Lemma to_pair_free_closed :
  ∀ e, 
  closed e -> 
  closed (to_pair_free e).
Proof. 
  intros.
  induction e; simpl; 
  intros x_contra H_contra; 
  try (apply H with (x:=x_contra); apply H_contra; fail).
  - (* E_App *)
    inversion H_contra; 
    apply closed_app in H as [H_c_e₁ H_c_e₂]; 
    subst; unfold closed in *.
    + eapply IHe1; eauto with local_hints.  
    + eapply IHe2; eauto with local_hints.
  - (* E_Fun *)
    unfold closed in H.
    apply H with x_contra.
    destruct (String.eqb_spec x x_contra).
    + subst. inversion H_contra; subst. contradiction H2. reflexivity.
    + inversion H_contra; subst. eauto with local_hints.
  - inversion H_contra; 
    apply closed_if in H as [H_c_e₁ [H_c_e₂ H_c_e₃]]; 
    subst; unfold closed in *.
    + eapply IHe1; eauto with local_hints.  
    + eapply IHe2; eauto with local_hints.
    + eapply IHe3; eauto with local_hints.
  - inversion H_contra; subst.
    + apply closed_let in H.
      eapply (IHe1 H); eauto.
    + apply H with x_contra.
      eauto with local_hints.
  - inversion H_contra; 
    apply closed_minus in H as [H_c_e₁ H_c_e₂]; 
    subst; unfold closed in *.
    + eapply IHe1; eauto with local_hints.  
    + eapply IHe2; eauto with local_hints.
  - inversion H_contra; 
    apply closed_eq in H as [H_c_e₁ H_c_e₂]; 
    subst; unfold closed in *.
    + eapply IHe1; eauto with local_hints.  
    + eapply IHe2; eauto with local_hints.
  - inversion H_contra; 
    apply closed_pair in H as [H_c_e₁ H_c_e₂]; 
    subst; unfold closed in *.
    + inversion H_contra; subst.
      * inversion H1; subst.
        inversion H2.
        eapply IHe2; eauto.
      * eapply IHe1; eauto with local_hints.     
    + eapply IHe1; eauto with local_hints.
  - apply closed_first in H.
    inversion H_contra.
    eapply IHe; eauto with local_hints.
  - apply closed_second in H.
    inversion H_contra.
    eapply IHe; eauto with local_hints.
  - apply closed_record in H as  [H_c_e₁ H_c_e₂].
    inversion H_contra; subst.
    + eapply IHe2; eauto with local_hints.  
    + eapply IHe1; eauto with local_hints.
  - apply closed_access in H.
    inversion H_contra; subst.
    eapply IHe; eauto with local_hints.
  - apply closed_fix in H.
    inversion H_contra; subst.
    eapply IHe; eauto with local_hints.
  - apply closed_in_left in H. inversion H_contra; subst. 
    eapply IHe; eauto with local_hints.
  - apply closed_in_right in H. inversion H_contra; subst. 
    eapply IHe; eauto with local_hints.
  - apply closed_match in H as [H1 [H2 H3]]. 
    inversion H_contra; subst.
    + apply IHe1 in H1. apply (H1 x_contra). assumption.
    + apply IHe2 in H2. apply (H2 x_contra). assumption.
    + apply IHe3 in H3. apply (H3 x_contra). assumption.
  - apply closed_sum_constr in H.
    apply IHe in H.
    inversion H_contra; subst.
    apply H with (x:=x_contra).
    apply H1. 
Qed.
  
Hint Resolve to_pair_free_closed : local_hints.

Lemma to_pair_free_subst :
  ∀ s x e e',
  substitution s x e e' ->
  substitution (to_pair_free s) x (to_pair_free e) (to_pair_free e').
Proof.
  intros.
  induction H; simpl; eauto with local_hints.
Qed.

Hint Resolve to_pair_free_subst : local_hints.

Lemma to_pair_free_lookup :
  ∀ x e e',
  lookup_val_record x e = Some e' ->
  lookup_val_record x (to_pair_free e) = Some (to_pair_free e').
Proof with eauto with local_hints.
  intros.
  induction e; inversion H...
  simpl.
  destruct (String.eqb_spec x x0); subst...
  inversion H1...
Qed.

Hint Resolve to_pair_free_lookup : local_hints.

Lemma pair_free_step :
  ∀ e e', 
  e --> e' -> 
  to_pair_free e --> to_pair_free e'.
Proof with eauto with local_hints.
  intro e.
  induction e; intros e' H_step; simpl; try (inversion H_step; subst; eauto with local_hints; fail)...
  inversion H_step; subst...
  simpl.
  apply ST_Fix_Fun.
  apply to_pair_free_subst in H0...
Qed.
Require Import Types.



Fixpoint to_pair_free_env (Γ : context) :=
  match Γ with 
  | Maps.empty => Maps.empty
  | Maps.update tail x t => Maps.update (to_pair_free_env tail) x (to_pair_free_type t) 
  end.

Fixpoint to_pair_free_constrs (constrs : list (type * string)) := 
  match constrs with 
  | [] => []
  | h::t =>  (to_pair_free_type (fst h), snd h)::to_pair_free_constrs t
  end.

Fixpoint to_pair_free_sum_env (Σ : sum_types_constructors) :=
  match Σ with 
  | [] => []
  | h::t => 
      (fst h, to_pair_free_constrs (snd h))::to_pair_free_sum_env t
  end.

Lemma pair_free_env_fin :
  ∀ (Γ : context) x t,
  Γ ? x = Some t ->
  (to_pair_free_env Γ) ? x = Some (to_pair_free_type t).
Proof.
  intros.
  induction Γ.
  - inversion H.
  - destruct (String.eqb_spec key x); subst; simpl.
    + inversion H. rewrite String.eqb_refl in *. inversion H1. subst. reflexivity.
    + rewrite Maps.update_neq in *; eauto. Check String.eqb_neq.
      rewrite <- String.eqb_neq in n. rewrite n. auto.
Qed.

Hint Resolve pair_free_env_fin : local_hints.

Lemma to_pair_free_record_is_record :
  ∀ t, 
  record_type t -> 
  record_type (to_pair_free_type t).
Proof.
  induction t; intros; inversion H; simpl; subst; eauto with local_hints.
Qed.

Hint Resolve to_pair_free_record_is_record : local_hints.

Lemma lookup_type_to_pair_free :
  ∀ x t t_res, 
  lookup_type_record x t = Some t_res ->
  lookup_type_record x (to_pair_free_type t) = Some (to_pair_free_type t_res).
Proof with eauto with local_hints.
  intros.
  induction t; inversion H.
  simpl in *.
  destruct (String.eqb_spec x x0); subst...
  inversion H1; subst...
Qed.

Hint Resolve lookup_type_to_pair_free : local_hints.

Lemma lookup_type_constrs_to_pair_free :
  ∀ name constrs t, 
  lookup_type_constrs name constrs = Some t -> 
  lookup_type_constrs name (to_pair_free_constrs constrs) = Some (to_pair_free_type t).
Proof.
  intros.
  induction constrs.
  - inversion H.
  - simpl in *. 
    destruct (String.eqb_spec (snd a) name).
    + inversion H. reflexivity.
    + apply IHconstrs. apply H.
Qed.


Lemma lookup_type_constrs_to_pair_free_none :
  ∀ name constrs, 
  lookup_type_constrs name constrs = None -> 
  lookup_type_constrs name (to_pair_free_constrs constrs) = None.
Proof.
  intros.
  induction constrs.
  - reflexivity.
  - simpl in *. 
    destruct (String.eqb_spec (snd a) name).
    + inversion H.
    + apply IHconstrs. apply H.
Qed.

Lemma lookup_type_sum_to_pair_free :
  ∀ Σ constr name t, 
  lookup_type_sum constr Σ = Some (name, t) -> 
  lookup_type_sum constr (to_pair_free_sum_env Σ) = Some (name, to_pair_free_type t).
Proof.
  intros.
  induction Σ.
  - inversion H.
  - simpl.
    destruct (lookup_type_constrs constr (snd a)) eqn:Heq.
    + destruct a.
      simpl in H.
      simpl in Heq. rewrite Heq in H. inversion H; subst.
      apply lookup_type_constrs_to_pair_free in Heq as Heq2. simpl. rewrite Heq2. reflexivity.
    + simpl in H. rewrite Heq in H.
      apply lookup_type_constrs_to_pair_free_none in Heq as Heq2. rewrite Heq2. apply IHΣ. assumption.
Qed.

Hint Resolve lookup_type_sum_to_pair_free : local_hints.


Theorem pair_free_type :
  ∀ Σ Γ e t,
  has_type Σ Γ e t -> 
  has_type 
    (to_pair_free_sum_env Σ) 
    (to_pair_free_env Γ) 
    (to_pair_free e) 
    (to_pair_free_type t).
Proof with eauto 3 with local_hints.
  intros * H_type.
  induction H_type; subst...
  eauto 4 with local_hints.
Qed.


Inductive record_free_type : type -> Prop := 
  | RFT_Num : record_free_type Type_Num
  | RFT_Bool : record_free_type Type_Bool
  | RFT_Fun :
      ∀ t₁ t₂, 
      record_free_type t₁ ->
      record_free_type t₂ ->
      record_free_type (Type_Fun t₁ t₂)
  | RFT_Prod :
      ∀ t₁ t₂, 
      record_free_type t₁ ->
      record_free_type t₂ ->
      record_free_type (Type_Prod t₁ t₂)
  | RFT_Union :
      ∀ t₁ t₂, 
      record_free_type t₁ ->
      record_free_type t₂ ->
      record_free_type (Type_Disjoint_Union t₁ t₂)
.

Inductive record_free_expr : expr -> Prop := 
  | RFE_Var : ∀ x, record_free_expr (E_Var x)
  | RFE_App : 
      ∀ e₁ e₂, 
      record_free_expr e₁ -> 
      record_free_expr e₂ -> 
      record_free_expr (E_App e₁ e₂)
  | RFE_Fun : 
      ∀ x t e, 
      record_free_type t -> 
      record_free_expr e -> 
      record_free_expr (E_Fun x t e)
  | RFE_True : record_free_expr E_True
  | RFE_False : record_free_expr E_False
  | RFE_If : 
      ∀ e₁ e₂ e₃, 
       record_free_expr e₁ -> 
       record_free_expr e₂ -> 
       record_free_expr e₃ ->
       record_free_expr (E_If e₁ e₂ e₃)
  | RFE_Let : 
      ∀ x e₁ e₂, 
       record_free_expr e₁ -> 
       record_free_expr e₂ -> 
       record_free_expr (E_Let x e₁ e₂)
  | RFE_Num : ∀ z, record_free_expr (E_Num z)
  | RFE_Minus : 
      ∀ e₁ e₂,
      record_free_expr e₁ ->
      record_free_expr e₂ ->
      record_free_expr (E_Minus e₁ e₂)
  | RFE_Eq : 
      ∀ e₁ e₂,
      record_free_expr e₁ ->
      record_free_expr e₂ ->
      record_free_expr (E_Eq e₁ e₂)
  | RFE_Pair : 
      ∀ e₁ e₂,
      record_free_expr e₁ ->
      record_free_expr e₂ ->
      record_free_expr (E_Pair e₁ e₂)
  | RFE_First : 
      ∀ e,
      record_free_expr e ->
      record_free_expr (E_First e)
  | RFE_Second : 
      ∀ e,
      record_free_expr e ->
      record_free_expr (E_Second e)
  | RFE_Access : (* À voir si on laisse *)
      ∀ e x,
      record_free_expr e ->
      record_free_expr (E_Record_Access e x)
  | RFE_Fix :
      ∀ e, 
      record_free_expr e ->
      record_free_expr (E_Fix e)
  | RFE_Inl :
      ∀ t₁ t₂ e, 
      record_free_type t₁ -> 
      record_free_type t₂ -> 
      record_free_expr e ->
      record_free_expr (E_Fix e)
  | RFE_Inr :
      ∀ t₁ t₂ e, 
      record_free_type t₁ -> 
      record_free_type t₂ -> 
      record_free_expr e ->
      record_free_expr (E_Fix e)
  | RFE_Match : 
      ∀ e₁ e₂ e₃, 
       record_free_expr e₁ -> 
       record_free_expr e₂ -> 
       record_free_expr e₃ ->
       record_free_expr (E_Match e₁ e₂ e₃)
.


Inductive record_free_env : context -> Prop := 
  | record_free_empty :
      record_free_env empty
  | record_free_add :
      ∀ (Γ : context) (x : string) (t : type),
      record_free_env Γ -> 
      record_free_type t -> 
      record_free_env (x |-> t; Γ)
.




(* 

  to_pair_free_type (Γ ? x) = (to_pair_free_env Γ) ? x
 *)


(* Goal ∀ Γ x t, 
  (to_pair_free_env Γ) ? x = Some (to_pair_free_type t) -> 
  Γ ? x = Some t.
Proof.
  induction Γ; intros.
  - inversion H.
  - simpl in *.
    destruct (String.eqb_spec key x); subst.
    + inversion H.
    + apply IHΓ. assumption.
Qed. *)
(* 
  Rajouter que le record {"first" : ..., "second":...} est réservé
  ou
  interdire les record dans Γ e et t

 *)
Goal  ∀ Σ Γ e t,
  record_free_type t -> 
  record_free_env Γ -> 
  record_free_expr e -> 
  has_type 
    Σ 
    (to_pair_free_env Γ) 
    (to_pair_free e) 
    (to_pair_free_type t) 
    ->
  has_type Σ Γ e t.
Proof.
  (* intros Γ e.
  generalize dependent Γ.
  induction e; intros.
  - (* E_Var *)
    simpl in H.
    induction t.
    + simpl in *.
      {
      induction Γ.
      - simpl in *. inversion H2; subst. inversion H5.
      - inversion H0; subst.
        apply T_Var. simpl.
        simpl in H2. inversion H2; subst. simpl in H6.
        destruct (String.eqb_spec key x).
        + subst. inversion H6. destruct val; try (inversion H4; fail).
          simpl in *. reflexivity.
        + apply IHΓ in H5.
          * inversion H5. assumption. 
          * apply T_Var.
            inversion H2; subst. simpl in H8. rewrite <- (String.eqb_neq key x) in n. rewrite n in H8. assumption.
      }
    + simpl in *.
      {
        induction Γ.
        - simpl in *. inversion H2; subst. inversion H5.
        - inversion H0; subst.
          apply T_Var. simpl.
          simpl in H2. inversion H2; subst. simpl in H6.
          destruct (String.eqb_spec key x).
          + subst. inversion H6. destruct val; try (inversion H4; fail).
            simpl in *. reflexivity.
          + apply IHΓ in H5.
            * inversion H5. assumption. 
            * apply T_Var.
              inversion H2; subst. simpl in H8. rewrite <- (String.eqb_neq key x) in n. rewrite n in H8. assumption.
        }
    + simpl in *.
      {
        induction Γ.
        - simpl in *. inversion H2; subst. inversion H5.
        - inversion H; subst. 
          clear H.
          inversion H0; subst.
          clear H0.
          inversion H2; subst.
          clear H2.
          apply IHΓ in H4.

        } *)
       
Admitted.

(* 

  Prouver les 2 théorèmes dans l'autre sens
  (potentiellement + compliqué)

*)