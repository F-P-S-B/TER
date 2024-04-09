(*
  Tight Typings and Split Bounds,
    BENIAMINO ACCATTOLI
    STÉPHANE GRAHAM-LENGRAND
    DELIA KESNER
  https://arxiv.org/pdf/1807.02358.pdf
*)
From Coq Require Import Unicode.Utf8.


Require Import String.
Require Import Arith.
From Coq Require Import Unicode.Utf8.


Inductive term : Set :=
  | T_Var (n : nat)
  | T_App (t₁ t₂ : term)
  | T_Abs (t : term)
.

Declare Custom Entry term.
Notation "<{ e }>" := e (e custom term at level 99).
 Notation "( x )" := x (in custom term, x at level 99).
Notation "'`' e '`'" := e (in custom term at level 0, e constr).
Notation "x" := x (in custom term at level 0, x constr at level 0).
Notation "'#' n" := (T_Var n) (in custom term at level 0).
 Notation "x y" := (T_App x y) (in custom term at level 2, left associativity).
Notation "'λ' t" := (T_Abs t) (
  in custom term at level 90, 
  t custom term at level 99,
  left associativity
).

Check <{ (λ #0 #0)(λ #0 #0) }>.

Fixpoint shift_indices (n : nat) (t : term) : term :=
  match t with
  | <{#v}> => if v <? n then <{#v}> else <{#`v+n`}>
  | <{λ t}> => <{λ `shift_indices n t`}>
  | <{t1 t2}> => <{`shift_indices n t1` `shift_indices n t2`}>
  end.

Search (nat -> nat -> bool).

Fixpoint subst_aux (n : nat) (s : term) (t : term) : term :=
  match t with 
  | <{#v}> => 
      if (n =? v)%nat 
      then s
      else if (v <? n) 
            then <{#v}>
            else <{#`v - 1`}>
  | <{λ t}> => <{λ `subst_aux (n+1) (shift_indices 1 s) t`}>
  | <{t1 t2}> => <{`subst_aux n s t1` `subst_aux n s t2`}>
  end.

  Definition subst (s : term) (t : term) : term := subst_aux 0 s t.


Notation "t '[' s ']'" := (subst s t) (in custom term at level 1, s at level 99, no associativity).

Check <{ λ λ ((λ #2 #1 #0) (λ #0))  }>.

Check  <{(λ λ ((#2 #1 #0) [λ #0]))}>.
Eval compute in <{(λ λ ((#2 #1 #0)[λ #0]))}>.



Definition deterministic {A} (relation : A -> A -> Prop) : Prop :=
  ∀ a a₁ a₂, relation a a₁ -> relation a a₂ -> a = a₂. 

Definition rel_normal {A} (relation : A -> A -> Prop) (a : A) : Prop := 
  ¬ ∃ b, relation a b.

(* 
  Definition 2.1 (Evaluation system)
 *)

Section EvalSystem.
Variable T : Set.
Variable relation : T -> T -> Prop.
Variable (normal neutral abs : T -> Prop).

Definition evaluation_system : Prop :=
        deterministic relation
    /\  (∀ t, rel_normal relation t <-> normal t) 
    /\  (∀ t, neutral t <-> (normal t /\ ¬ abs t))
.

End EvalSystem.

Check evaluation_system.


Inductive reflexive_closure {A} (rel : A -> A -> Prop) : A -> A -> Prop :=
  | RC_refl : ∀ t, reflexive_closure rel t t 
  | RC_self : ∀ t₁ t₂,
    rel t₁ t₂ -> 
    reflexive_closure rel t₁ t₂
.

Inductive transitive_closure {A} (rel : A -> A -> Prop) : A -> A -> Prop := 
  | TC_self :  
      ∀ t₁ t₂,
      rel t₁ t₂ -> 
      transitive_closure rel t₁ t₂
  | TC_trans :
      ∀ t₁ t₂ t₃, 
      transitive_closure rel t₁ t₂ ->
      transitive_closure rel t₂ t₃ ->
      transitive_closure rel t₁ t₃
.

Inductive n_iteration {A} (rel : A -> A -> Prop) : nat -> A -> A -> Prop := 
  | NI_O : ∀ t, n_iteration rel O t t 
  | NI_Sn : 
      ∀ n t₁ t₂ t₃, 
      rel t₁ t₂ -> 
      n_iteration rel n t₂ t₃ ->
      n_iteration rel (S n) t₁ t₃
.