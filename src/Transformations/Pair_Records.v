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

Fixpoint is_pair_free (e : expr) : Prop :=
  match e with 
  | <{true}> | <{false}> 
  | E_Num _  | <{ unit }>
  | <{#_}> => 
      True
  | <{e₁ e₂}> 
  | <{e₁ - e₂}>  
  | <{e₁ == e₂}>  
  | <{let _ = e₁ in e₂}> => 
       is_pair_free e₁ /\ is_pair_free e₂
  | <{fun _ : _ => e}> => is_pair_free e
  | <{if e₁ then e₂ else e₃}> 
  | <{match e₁ with | inl => e₂ | inr => e₃ end}> => 
      is_pair_free e₁ /\ is_pair_free e₂ /\ is_pair_free e₃
  | <{(_, _)}>  
  | <{first _}> | <{second _}> => False
  | <{ e::_ }> | <{fix e}> 
  | <{ inl < _ | _> e }> | <{ inr < _ | _> e }> 
  | E_Sum_Constr _ e => 
      is_pair_free e
  | <{ { lse } }> => is_pair_free_lsexpr lse
  | <{match_sum e with ls : default end_sum}> => 
      is_pair_free e /\ is_pair_free default /\ is_pair_free_lsexpr ls
  end
with 
  is_pair_free_lsexpr (lse : lsexpr) := 
    match lse with 
    | <{ nil }> => True
    | <{ _ := e; tail }> => is_pair_free e /\ is_pair_free_lsexpr tail
    end
.



Fixpoint to_pair_free_type (t : type) : type :=
  match t with
  | {{ Bool }}=> {{ Bool }}
  | {{ Int }} => {{ Int }}
  | {{ Unit }} => {{ Unit }}
  | {{ t₁ -> t₂ }} => {{ `to_pair_free_type t₁` -> `to_pair_free_type t₂` }}
  | {{ t₁ * t₂ }} => 
      let fst := "first"%string in
      let snd := "second"%string in
      {{ {fst : `to_pair_free_type t₁` ; snd : `to_pair_free_type t₂`; Nil } }}
  | {{ { tᵣ } }} => {{ { `to_pair_free_lstype tᵣ` } }}
  | {{ t₁ + t₂ }} => {{ `to_pair_free_type t₁` + `to_pair_free_type t₂` }}
  | Type_Sum name => Type_Sum name
  end
with to_pair_free_lstype (lst : lstype) : lstype :=
  match lst with 
  | {{ Nil }} => {{ Nil }}
  | {{ x : t ; tᵣ }} => 
      {{ x : `to_pair_free_type t` ; `to_pair_free_lstype tᵣ` }}
  end
  .

Fixpoint to_pair_free (e : expr) : expr :=
  match e with 
  | <{ #x }> => <{ #x }>
  | <{ e₁ e₂ }> => <{ `to_pair_free e₁` `to_pair_free e₂` }> 
  | <{ fun x : t => e }> => <{ fun x : `to_pair_free_type t` => `to_pair_free e`}>
  | <{ true }> => <{ true }>
  | <{ false }> => <{ false }>
  | <{ if e₁ then e₂ else e₃ }> => <{
        if `to_pair_free e₁` then `to_pair_free e₂` else `to_pair_free e₃`
      }>  
  | <{ let x = e₁ in e₂ }> => <{ let x = `to_pair_free e₁` in `to_pair_free e₂` }>
  | E_Num z => E_Num z
  | <{ e₁ - e₂ }> => <{ `to_pair_free e₁` - `to_pair_free e₂` }>
  | <{ e₁ == e₂ }> => <{ `to_pair_free e₁` == `to_pair_free e₂` }>
  | <{ (e₁, e₂) }> => 
      let fst := "first"%string in
      let snd := "second"%string in
      <{ { fst := `to_pair_free e₁` ; snd := `to_pair_free e₂` ; nil } }>
  | <{ first e }> => let fst := "first"%string in <{ `to_pair_free e`::fst }>
  | <{ second e }> => let snd := "second"%string in <{ `to_pair_free e`::snd }>
  | <{ { rec } }> => <{ { `to_pair_free_lsexpr rec` } }>
  | <{ e :: x }> => <{ `to_pair_free e` :: x }>
  | <{ fix e }> => <{ fix `to_pair_free e` }>
  | <{ inl < t₁ | t₂ > e }> => 
      <{ inl < `to_pair_free_type t₁` | `to_pair_free_type t₂` > `to_pair_free e` }>
  | <{ inr < t₁ | t₂ > e }> => 
      <{ inr < `to_pair_free_type t₁` | `to_pair_free_type t₂` > `to_pair_free e` }>
  | <{ match e with | inl => eₗ | inr => eᵣ end }> => <{ 
        match `to_pair_free e` with 
        | inl => `to_pair_free eₗ` 
        | inr => `to_pair_free eᵣ` 
        end 
      }> 
  | <{ unit }> => <{ unit }>
  | E_Sum_Constr name e => E_Sum_Constr name (to_pair_free e)
  | <{ match_sum e with branches : default end_sum }> =><{ 
        match_sum `to_pair_free e` with 
        `to_pair_free_lsexpr branches` 
        : `to_pair_free default` 
        end_sum 
      }>
  end
with to_pair_free_lsexpr (lse : lsexpr) : lsexpr := 
    match lse with 
    | <{ nil }> => <{ nil }>
    | <{ x := e; tail }> => <{ x := `to_pair_free e` ; `to_pair_free_lsexpr tail` }>
    end.

Hint Unfold is_pair_free : local_hints.
Hint Unfold is_pair_free_lsexpr : local_hints.
Definition t_pair_bool := Type_Prod Type_Num Type_Bool.


Definition x := "x"%string.
Definition y := "y"%string.
Definition z := "z"%string.

Compute (to_pair_free <{ first (second #x , first #y)}>).

Lemma to_pair_free_is_pair_free :
  ∀ e,
  is_pair_free (to_pair_free e).
Proof.
  intro e.
  pose (
    P (e : expr) :=
      is_pair_free (to_pair_free e)
  ).
  pose (
    P0 (l : lsexpr) :=
      is_pair_free_lsexpr (to_pair_free_lsexpr l)
  ).
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0; clear P P0;
  intros; simpl in *; eauto with local_hints.
Qed.

Hint Resolve to_pair_free_is_pair_free : local_hints.

Lemma to_pair_free_free:
  ∀ e xf, 
  is_free_in xf (to_pair_free e) -> 
  is_free_in xf e.
Proof with eauto with local_hints. 
  intro e.
  pose (
    P (e : expr) :=
      ∀ xf,
      is_free_in xf (to_pair_free e) -> 
      is_free_in xf e
  ).
  pose (
    P0 (l : lsexpr) :=
      ∀ xf,
      is_free_in_lsexpr xf (to_pair_free_lsexpr l) -> 
      is_free_in_lsexpr xf l
  ).
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0; clear P P0; simpl in *;
  try (intros * IH1 * IH2 * IH3 * [H_free | [H_free | H_free]]);
  try (intros * IH1 * IH2 * IH3 * H_free);
  try (intros * IH1 * IH2 * [H_free | H_free]);
  try (intros * IH1 * IH2 * H_free);
  try (intros * IH1 * H_free);
  try (intros * H_free);
  try (inversion H_free)...
  exfalso...
Qed.

Hint Resolve to_pair_free_free : local_hints.


Lemma to_pair_free_value:
  ∀ e, 
  value e -> 
  value (to_pair_free e).
Proof with eauto 6 with local_hints. 
  intro e.
  pose (P (e : expr) := value e -> value (to_pair_free e)).
  pose (P0 (l : lsexpr) := value_lsexpr l -> value_lsexpr (to_pair_free_lsexpr l));
  apply expr_mut_ind with (P := P) (P0 := P0); unfold P; unfold P0; clear P P0; simpl in *;
  try (intros * IH1 * IH2 * IH3 * H_val);
  try (intros * IH1 * IH2 * H_val);
  try (intros * IH1 * H_val);
  try (intros * H_val);
  try (inversion H_val; subst)...
Qed.
Hint Resolve to_pair_free_value : local_hints.

Lemma to_pair_free_value_lsexpr:
  ∀ l, 
  value_lsexpr l -> 
  value_lsexpr (to_pair_free_lsexpr l).
Proof with eauto 6 with local_hints. 
  induction l...
  intro H_val.
  inversion H_val; subst...
Qed.
Hint Resolve to_pair_free_value_lsexpr : local_hints.

Lemma to_pair_free_closed :
  ∀ e, 
  closed e -> 
  closed (to_pair_free e).
Proof with eauto with local_hints. 
  intro e.
  pose (
    P (e : expr) := 
      closed e -> 
      closed (to_pair_free e)
  ).
  pose (
    P0 (l : lsexpr) := 
      closed_lsexpr l -> 
      closed_lsexpr (to_pair_free_lsexpr l)
  ).
  
  apply expr_mut_ind with (P := P) (P0 := P0);
  unfold P; unfold P0; clear P P0; simpl in *;
  try (intros * IH1 * IH2 * IH3 * H_closed x_contra H_contra);
  try (intros * IH1 * IH2 * H_closed x_contra H_contra);
  try (intros * IH1 * H_closed x_contra H_contra);
  try (intros * H_closed x_contra H_contra);
  try (inversion H_contra; eapply H_closed; eauto with local_hints; fail);
  try (
    unfold closed in *; simpl in *; 
    unfold closed_lsexpr in *; simpl in *; 
    try apply IH1 with x_contra in H_closed; 
    try apply IH2 with x_contra in H_closed; 
    try apply IH3 with x_contra in H_closed; 
    eauto with local_hints; contradiction; fail
  ).
  unfold closed in *; simpl in *; 
  unfold closed_lsexpr in *; simpl in *.
  inversion H_contra.
  - apply H_closed with x_contra...
  - eapply IH2... intros x_contra' H_contra'.
    apply H_closed with x_contra'...
Qed.
Hint Resolve to_pair_free_closed : local_hints.

Lemma to_pair_free_subst :
  ∀ e s x e',
  substitution s x e e' ->
  substitution (to_pair_free s) x (to_pair_free e) (to_pair_free e').
Proof with eauto with local_hints. 
  intro e.
  pose (
    P (e : expr) := 
      ∀ s x e',
      substitution s x e e' ->
      substitution (to_pair_free s) x (to_pair_free e) (to_pair_free e')
  ).
  pose (
    P0 (l : lsexpr) := 
      ∀ s x l',
      substitution_lsexpr s x l l' ->
      substitution_lsexpr (to_pair_free s) x (to_pair_free_lsexpr l) (to_pair_free_lsexpr l')
  ).
  
  apply expr_mut_ind with (P := P) (P0 := P0);
  unfold P; unfold P0; clear P P0; simpl in *;
  try (intros * IH1 * IH2 * IH3 * H_subst);
  try (intros * IH1 * IH2 * H_subst);
  try (intros * IH1 * H_subst);
  try (intros * H_subst);
  try (inversion H_subst; eauto 6 with local_hints; fail).
Qed.

Hint Resolve to_pair_free_subst : local_hints.


Lemma to_pair_free_lookup_some :
  ∀ l x e',
  lookup_lsexpr x l = Some e' ->
  lookup_lsexpr x (to_pair_free_lsexpr l) = Some (to_pair_free e').
Proof with eauto with local_hints.
  induction l.
  - intros * H_lookup. inversion H_lookup.
  - intros * H_lookup. 
    simpl in *.
    destruct (String.eqb_spec s x0); subst...
    inversion H_lookup...
Qed.

Lemma to_pair_free_lookup_none :
  ∀ l x,
  lookup_lsexpr x l = None ->
  lookup_lsexpr x (to_pair_free_lsexpr l) = None.
Proof with eauto with local_hints.
  induction l...
  intros * H_lookup. 
  simpl in *.
  destruct (String.eqb_spec s x0); subst...
  inversion H_lookup.
Qed.

Hint Resolve to_pair_free_lookup_some : local_hints.
Hint Resolve to_pair_free_lookup_none : local_hints.


Lemma pair_free_step :
  ∀ e e', 
  e --> e' -> 
  to_pair_free e --> to_pair_free e'.
Proof with eauto with local_hints.
  intro e.
  pose (
    P (e : expr) := 
      ∀ e',
      e --> e' -> 
      to_pair_free e --> to_pair_free e'
  ).
  pose (
    P0 (l : lsexpr) := 
      ∀ l',
      l -->ₗ l' -> 
      to_pair_free_lsexpr l -->ₗ to_pair_free_lsexpr l'
  ).
  apply expr_mut_ind with (P := P) (P0 := P0);
  unfold P; unfold P0; clear P P0; simpl in *;
  try (intros * IH1 * IH2 * IH3 * H_step);
  try (intros * IH1 * IH2 * H_step);
  try (intros * IH1 * H_step);
  try (intros * H_step);
  try (inversion H_step; subst; simpl in *; eauto 6 with local_hints; fail).
  inversion H_step; subst...
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
Proof with eauto with local_hints.
  intros * H_find.
  induction Γ.
  - inversion H_find.
  - simpl in *. destruct (String.eqb_spec key x0); subst...
    inversion H_find; subst. reflexivity.
Qed.

Hint Resolve pair_free_env_fin : local_hints.


Lemma lookup_type_to_pair_free :
  ∀ x t t_res, 
  lookup_lstype x t = Some t_res ->
  lookup_lstype x (to_pair_free_lstype t) = Some (to_pair_free_type t_res).
Proof with eauto with local_hints.
  intros.
  induction t; inversion H.
  simpl in *.
  destruct (String.eqb_spec x1 x0); subst...
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
  ∀ e Σ Γ t,
  Σ / Γ |- e : t -> 
  (to_pair_free_sum_env Σ) / (to_pair_free_env Γ) 
  |- `to_pair_free e` : (to_pair_free_type t).
Proof with eauto 4 with local_hints.
  intro e.
  pose (
    P (e : expr) := 
      ∀ Σ Γ t,
      Σ / Γ |- e : t -> 
      (to_pair_free_sum_env Σ) / (to_pair_free_env Γ) 
      |- `to_pair_free e` : (to_pair_free_type t)
  ).
  pose (
    P0 (l : lsexpr) := 
      ∀ Σ Γ, (
        ∀ name_sum t,
        Σ / Γ |-ₛ name_sum ~> l : t -> 
        (to_pair_free_sum_env Σ) / (to_pair_free_env Γ) 
          |-ₛ name_sum ~> `to_pair_free_lsexpr l` : (to_pair_free_type t)
      ) /\ (
        ∀  t,
        Σ / Γ |-ᵣ l : t -> 
        (to_pair_free_sum_env Σ) / (to_pair_free_env Γ) 
          |-ᵣ `to_pair_free_lsexpr l` : (to_pair_free_lstype t)
      )      
  ).
  apply expr_mut_ind with (P := P) (P0 := P0);
  unfold P; unfold P0; clear P P0; simpl in *;
  try (intros * IH1 * IH2 * IH3 * H_type);
  try (intros * IH1 * IH2 * H_type);
  try (intros * IH1 * IH2 *; split; intros * H_type);
  try (intros * IH1 * H_type);
  try (intros *; split; intros * H_type);
  try (intros * H_type);
  try (inversion H_type; subst);
  try (apply IH1 in H3; apply IH2 in H5; eauto 4 with local_hints; fail);
  try (apply IH1 in H2; eauto 4 with local_hints; fail);
  try (apply IH1 in H3; eauto 4 with local_hints; fail);
  try (apply IH1 in H4; eauto 4 with local_hints; fail);
  try (apply IH1 in H5; eauto 4 with local_hints; fail);
  eauto 2 with local_hints.
  - simpl... 
  - apply IH2 in H6...
  - apply IH1 in H4; apply IH2 in H6; apply IH3 in H7...
  - apply IH1 in H4; apply IH2 in H6; apply IH3 in H7...
  - apply IH1 in H8. 
    edestruct IH2...
  - apply IH1 in H6.
    edestruct IH2...
Qed.