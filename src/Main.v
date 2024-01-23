From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Require Import Maps.

Create HintDb local_hints.

Inductive type :=
| Type_Bool
| Type_Fun (e1 e2 : type) : type
.



Inductive expr := 
| E_Var (x : string) 
| E_App (e1 e2 : expr) 
| E_Fun (x : string) (t : type) (e : expr) 
| E_True  
| E_False 
| E_If (e1 e2 e3 : expr)  
| E_Let (x : string) (e1 e2 : expr)
.

Inductive value : expr -> Prop :=
  | V_True : value E_True
  | V_False : value E_False
  | V_Fun : 
        forall 
            (x : string) 
            (t : type) 
            (e : expr), 
        value (E_Fun x t e)
  .

Inductive substitution (s : expr) (x : string) : expr -> expr -> Prop :=
    | S_Var_Eq :
        substitution s x (E_Var x) s
    | S_Var_Neq :
        forall (y : string), x <> y -> substitution s x (E_Var y) (E_Var y)
    | S_App : 
        forall (e1 e1' e2 e2' : expr),
        substitution s x e1 e1' ->
        substitution s x e2 e2' ->
        substitution s x (E_App e1 e2) (E_App e1' e2')
    | S_Fun_Eq : 
        forall (t : type) (e : expr),
        substitution s x (E_Fun x t e) (E_Fun x t e)
    | S_Fun_Neq : 
        forall (y : string) (t : type) (e e' : expr),
        x <> y -> substitution s x e e' -> 
        substitution s x (E_Fun y t e) (E_Fun y t e')
    | S_True : 
        substitution s x E_True E_True
    | S_False : 
        substitution s x E_False E_False
    | S_If : 
        forall (e1 e1' e2 e2' e3 e3' : expr),
        substitution s x e1 e1' ->
        substitution s x e2 e2' ->
        substitution s x e3 e3' ->
        substitution s x (E_If e1 e2 e3) (E_If e1' e2' e3')
    | S_Let_Eq : 
      forall (e1 e1' e2: expr),
      substitution s x e1 e1' -> 
      substitution s x (E_Let x e1 e2) (E_Let x e1' e2)
    | S_Let_Neq : 
      forall (y : string) (e1 e1' e2 e2': expr),
      x <> y ->
      substitution s x e1 e1' -> 
      substitution s x e2 e2' -> 
      substitution s x (E_Let y e1 e2) (E_Let y e1' e2')
.

Hint Constructors substitution : local_hints.

Lemma exists_subst : ∀ s x e, ∃ e', substitution s x e e'.
Proof with eauto.
    intros.
    induction e;
    try destruct IHe;
    try destruct IHe1;
    try destruct IHe2; 
    try destruct IHe3; 
    try destruct (String.eqb_spec x x0); 
    subst;
    eauto with local_hints.
Qed.



Inductive step : expr -> expr -> Prop := 
| ST_App_Fun : 
    forall (x : string) (t : type) (e e' v : expr),
    value v -> 
    substitution v x e e' ->
    step (E_App (E_Fun x t e) v) e'
| ST_App_Left : 
    forall (e1 e1' e2 : expr),
    step e1 e1' ->
    step (E_App e1 e2) (E_App e1' e2)
| ST_App_Right : 
    forall (v1 e2 e2' : expr),
    value v1 ->
    step e2 e2' ->
    step (E_App v1 e2) (E_App v1 e2')
| ST_If_True : 
    forall (e1 e2 : expr),
    step (E_If E_True e1 e2) e1
| ST_If_False : 
    forall (e1 e2 : expr),
    step (E_If E_False e1 e2) e2
| ST_If : 
    forall (e1 e1' e2 e3 : expr),
    step e1 e1' ->
    step (E_If e1 e2 e3) (E_If e1' e2 e3)
| ST_Let_Left : 
    forall (x : string) (e1 e1' e2 : expr),
    step e1 e1' ->
    step (E_Let x e1 e2) (E_Let x e1' e2)
| ST_Let_Right : 
    forall (x : string) (v1 e2 e2' : expr),
    value v1 ->
    substitution v1 x e2 e2' ->
    step (E_Let x v1 e2) e2'
.



Definition context := Maps.partial_map type.


Inductive has_type : context -> expr -> type -> Prop := 
| T_Var: forall Γ x t, 
            Γ x = Some t -> 
            has_type Γ (E_Var x) t

| T_Fun: forall Γ x t1 e t2,
            has_type (x |-> t1; Γ) e t2 ->
            has_type Γ (E_Fun x t1 e) (Type_Fun t1 t2)
| T_App: forall Γ e1 e2 t1 t2, 
            has_type Γ e2 t1 -> 
            has_type Γ e1 (Type_Fun t1 t2) ->
            has_type Γ (E_App e1 e2) t2

| T_True: forall Γ, 
            has_type Γ E_True Type_Bool
| T_False: forall Γ, 
            has_type Γ E_True Type_Bool

| T_If: forall Γ e1 e2 e3 t, 
            has_type Γ e1 Type_Bool -> 
            has_type Γ e2 t -> 
            has_type Γ e3 t -> 
            has_type Γ (E_If e1 e2 e3) t 
| T_Let : forall Γ x e1 e2 t1 t2, 
            has_type Γ e1 t1 -> 
            has_type (x |-> t1; Γ) e2 t2 -> 
            has_type Γ (E_Let x e1 e2) t2
.


Lemma weakening : ∀ Γ Γ' e t, 
    includedin Γ Γ' ->
    has_type Γ e t ->
    has_type Γ' e t.
Proof.
    intros * H_included H_type.
    generalize dependent Γ'.
    induction H_type; intros.
    - apply T_Var. apply H_included. assumption.
    - apply T_Fun. apply IHH_type.
      apply Maps.includedin_update. assumption.
    - eapply T_App; eauto.
    - apply T_True.         
    - apply T_False.
    - apply T_If; eauto.
    - eapply T_Let; eauto. 
      apply IHH_type2.
      apply Maps.includedin_update.
      assumption.
Qed.



Lemma weakening_empty : ∀ Γ e t, 
    has_type empty e t ->
    has_type Γ e t.
Proof.
intros. apply (weakening empty); auto.
intros x v contra. discriminate contra.
Qed.


Definition closed (e : expr) :=
  ∀ t, (∃ Γ, has_type Γ e t) -> ∀ Γ, has_type Γ e t.  (* Proposition de définition de clos *) 

Lemma subst_typing : ∀ Γ s x e e' t_e t_s, 
    has_type (x |-> t_s; Γ) e t_e ->
    has_type empty s t_s ->  
    substitution s x e e' -> 
    has_type Γ e' t_e.
Proof.
    intros * H_type_e H_type_s H_subst.
    generalize dependent t_e.
    generalize dependent t_s.
    generalize dependent Γ.
    induction H_subst; intros.
    - inversion H_type_e; subst. 
      rewrite Maps.update_eq in H1. inversion H1; subst.
      apply weakening_empty.
      assumption.
    - inversion H_type_e; subst. 
      apply T_Var. rewrite update_neq in H2; auto.
    - inversion H_type_e; subst. 
      eapply T_App; eauto.
    - inversion H_type_e; subst.
      apply T_Fun.   
      rewrite Maps.update_shadow in H4. assumption.    
    - inversion H_type_e; subst.
      apply T_Fun.
      rewrite Maps.update_permute in H5; auto.
      eapply IHH_subst; eauto.
    - inversion H_type_e; apply T_True.
    - inversion H_type_e; apply T_False.
    - inversion H_type_e; subst. apply T_If. eauto.
      + eapply IHH_subst2; eauto.
      + eapply IHH_subst3; eauto.
    - inversion H_type_e; subst. eapply T_Let; eauto.
      rewrite Maps.update_shadow in H5. auto.
    - inversion H_type_e; subst. eapply T_Let; eauto.
      rewrite Maps.update_permute in H6; auto.
      eapply IHH_subst2; eauto.
Qed.     

Lemma canonical_form_bool : ∀ e,
    has_type empty e Type_Bool -> 
    value e ->
    e = E_True \/ e = E_False.
Proof.
    intros * H_type H_val.
    inversion H_val; subst; auto.
    inversion H_type.
Qed.


Lemma canonical_form_fun : ∀ e t1 t2,
    has_type empty e (Type_Fun t1 t2) -> 
    value e ->
    ∃ x e', e = E_Fun x t1 e'. 
Proof.
    intros * H_type H_val.
    inversion H_val; subst; try (inversion H_type; fail).
    inversion H_type; subst.
    eauto.
Qed.


Theorem progress : ∀ e t,
    has_type empty e t -> 
    value e \/ ∃ e', step e e'.
Proof.
    intros * H_type.
    generalize dependent t.
    induction e; intros.
    - inversion H_type; subst. inversion H1.
    - right.
      inversion H_type; subst. 
      destruct (IHe1 (Type_Fun t1 t)) as [H_val_e1 | [e1' H_step_e1] ]; auto.
      + destruct (IHe2 t1) as [H_val_e2 | [e2' H_step_e2] ]; auto.
        * assert (H := canonical_form_fun e1 t1 t H4 H_val_e1).
          destruct H as [x [e' H_eq]]. subst.
          apply IHe1 in H4.
          destruct H4 as [H_val | H_ex].
          -- assert (H:= exists_subst e2 x e'). 
             destruct H as [e'0 H_sub].
             exists e'0.
             apply ST_App_Fun; auto. 
          -- destruct H_ex as [e'0 H_ex].
             exists (E_App e'0 e2). 
             apply ST_App_Left. assumption.
        * exists (E_App e1 e2'). apply ST_App_Right; auto.
      + exists (E_App e1' e2). apply ST_App_Left; auto.
    - left. apply V_Fun.
    - left. apply V_True. 
    - left. apply V_False.
    - right.
      inversion H_type; subst.
      apply IHe1 in H3 as H_e1_val_step.  
      apply IHe2 in H5 as H_e2_val_step.  
      apply IHe3 in H6 as H_e3_val_step.
      destruct H_e1_val_step as [H_val_e1 | [e' H_step]].
      + apply canonical_form_bool in H_val_e1; auto.
        destruct H_val_e1 as [H_e1_eq | H_e1_eq]; subst.
        * exists e2. apply ST_If_True.
        * exists e3. apply ST_If_False.
      + exists (E_If e' e2 e3). apply ST_If. assumption.
    - right. 
      inversion H_type; subst.
      destruct (IHe1 t1) as [H_val_e1 | [e1' H_step_e1] ]; auto.
      + assert (H:= exists_subst e1 x e2). 
        destruct H as [e' H_sub].
        exists e'.
        apply ST_Let_Right; auto.
      + exists (E_Let x e1' e2).
        apply ST_Let_Left. assumption.
Qed.  


Theorem preservation : forall e e' t,
  has_type empty e t  ->
  step e e'  ->
  has_type empty e' t.
Proof.
    intros * H_type_e. 
    generalize dependent e'.
    remember empty as Γ.
    induction H_type_e;
    intros e' H_step; try (inversion H_step; fail).
    - inversion H_step; subst.
      + inversion H_type_e2; subst. 
        apply (subst_typing empty e2 x e e' t2 t1); auto.   
      + apply T_App with t1; auto.
      + apply T_App with t1; auto.
    - inversion H_step; subst; auto.
      apply T_If; auto.
    - inversion H_step; subst.
      + apply T_Let with t1; auto.
      + apply (subst_typing _ e1 x e2 e') in H_type_e2; auto.   
Qed.     


(* 
  TODO:
    - ajouter arithmétique
    - Renforcer preservation et progress pour avoir un environnement Γ quelconque
      Idées: 
        - Ajouter une notion d'expressions closes, de variables libres 



 *)