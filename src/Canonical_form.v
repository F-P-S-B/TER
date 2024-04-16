From Coq Require Import Unicode.Utf8.
Require Import Hints.
Require Import Syntax.
Require Import Types.
Local Open Scope Z_scope.
Require Import ZArith.
Require Maps.
Import Maps.Notations.

Local Ltac solve_canon := 
    intros; 
    match goal with 
    | [ H_val : value _  , H_type : has_type _ _ _ _|- _] => 
        inversion H_val; subst; inversion H_type; eauto 6
    end.

Local Lemma t_num : 
    ∀ Γ Σ e,
    has_type Σ Γ  e  Type_Num ->  
    value e ->
    ∃ (z : Z), e = <{z}>.
Proof.
    solve_canon.
Qed.

Hint Resolve t_num : local_hints.

Local Lemma t_bool : 
    ∀ Γ Σ e,
    has_type Σ Γ  e  Type_Bool ->  
    value e ->
    e = <{true}> \/ e = <{false}>.
Proof.
    solve_canon.
Qed.

Hint Resolve t_bool : local_hints.

Local Lemma t_fun : 
    ∀ Γ Σ e t1 t2,
    has_type Σ Γ  e  (Type_Fun t1 t2) ->  
    value e ->
    ∃ x e', e = <{fun x : t1 => e'}>. 
Proof.
    solve_canon.
Qed.
Hint Resolve t_fun : local_hints.


Local Lemma t_pair :
    ∀ Γ Σ e t₁ t₂,
    has_type Σ Γ  e  (Type_Prod t₁ t₂) ->  
    value e ->
    ∃ e₁ e₂, e = <{(e₁, e₂)}>.
Proof.
    solve_canon.
Qed. 
Hint Resolve t_pair : local_hints.


Local Lemma t_record :
    ∀ Σ Γ (t : lstype) (e : expr),
    Σ / Γ |- e : {{ {t} }} ->
    value e -> 
    ∃ (rec : lsexpr), 
        e = <{ {rec} }> 
    /\  Σ / Γ |-ᵣ rec : t.
Proof.
  solve_canon.
Qed.

Local Lemma record_type_lookup :
  ∀ Γ Σ e t_rec t x, 
  Σ / Γ |-ᵣ e : t_rec -> 
  lookup_lstype x t_rec = Some t -> 
  ∃ e', lookup_lsexpr x e = Some e'.
Proof with eauto with local_hints.
  intros Γ Σ e t_rec.
  generalize dependent Γ.
  generalize dependent e.
  induction t_rec.
  - intros * H_type H_lookup. inversion H_lookup.
  - intros * H_type H_lookup.
    inversion H_type; subst.
    simpl in *.
    destruct (String.eqb x x0)...
Qed.

Hint Resolve record_type_lookup : local_hints.


Lemma record_val_lookup :
  ∀ Γ Σ e t_rec e' x, 
  Σ / Γ |-ᵣ e : t_rec -> 
  lookup_lsexpr x e = Some e' ->
  ∃ t, lookup_lstype x t_rec = Some t.
Proof with eauto with local_hints.
  intros Γ Σ e.
  generalize dependent Γ.
  induction e.
  - intros * H_type H_lookup. inversion H_lookup.
  - intros * H_type H_lookup.
    inversion H_type; subst.
    simpl in *.
    destruct (String.eqb s x) eqn:Heq...
Qed.

Hint Resolve record_val_lookup : local_hints.



Local Lemma t_in: 
    ∀ Γ Σ e t₁ t₂,
    has_type Σ Γ  e  (Type_Disjoint_Union t₁ t₂) ->  
    value e ->
    ∃ e', e = E_In_Left t₁ t₂ e' \/ e = E_In_Right t₁ t₂ e'.
Proof.
    solve_canon.    
Qed.
Hint Resolve t_in : local_hints.


Local Lemma t_enum :
    ∀ Γ Σ e name,
    has_type Σ Γ e (Type_Sum name) ->  
    value e ->
    ∃ constr e' t, 
       lookup_type_sum constr Σ = Some (name, t)
    /\ has_type Σ Γ e' t
    /\ e = <{constr[e']}>.
Proof.
    solve_canon.
Qed.
  

Hint Resolve t_enum : local_hints.

