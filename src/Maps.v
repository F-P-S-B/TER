(** * Maps: Total and Partial Maps *)
(* File taken from software foundations' "Programming language foundations" *)
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
Set Default Goal Selector "!".



(* ################################################################# *)
(** * Total Maps *)

(** We build up to partial maps in two steps.  First, we define a type
    of _total maps_ that return a default value when we look up a key
    that is not present in the map. *)
Inductive map {A} :=
| empty
| update (m : map) (key : string) (val : A) 
.

Fixpoint find {A} (m : map) (key : string) : option A :=
match m with 
| empty => None 
| update m k v => if (k =? key)%string then Some v else find m key
end.

(** We introduce a similar notation for partial maps: *)
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

(** We can also hide the last case when it is empty. *)
Notation "x '|->' v" := (update empty x v)
  (at level 100).

Notation "m '?' x" := (find m x)
  (at level 50, left associativity).

Axiom Maps_extensionnality :
 forall A (m1 m2 : @map A), (forall x, m1 ? x = m2 ? x) -> m1 = m2.
(** We now straightforwardly lift all of the basic lemmas about total
    maps to partial maps.  *)

Lemma apply_empty : forall (A : Type) (x : string),
  (@empty A) ? x = None.
Proof.
  intros. simpl.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : map) (x: string) (v: A),
  (x |-> v ; m) ? x = Some v.
Proof.
  intros. simpl.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : map) (x1 x2 : string) (v : A),
  x2 <> x1 ->
  (x2 |-> v ; m) ? x1 = m ? x1.
Proof.
  intros A m x1 x2 v H.
  rewrite <- String.eqb_neq in H.
  simpl. rewrite H.
  reflexivity.
Qed.

Lemma update_shadow : forall (A : Type) (m : map) (x : string) (v1 v2 : A),
  (x |-> v2 ; x |-> v1 ; m)  = (x |-> v2 ; m) .
Proof.
  intros A m x v1 v2. 
  apply Maps_extensionnality. intro y. simpl.
  destruct (String.eqb_spec x y); reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : map) (x : string) (v : A),
  m ? x = Some v ->
  (x |-> v ; m) = m .
Proof.
  intros A m x v H. apply Maps_extensionnality. intro y. simpl. rewrite <- H.
  destruct (String.eqb_spec x y); subst; reflexivity.
Qed.

Theorem update_permute : forall (A : Type) (m : map)
                                (x1 x2 : string) (v1 v2 : A),
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2 H.
  apply Maps_extensionnality. intro y.
  simpl.
  destruct (String.eqb_spec x1 y);
  destruct (String.eqb_spec x2 y); subst; auto.
  exfalso. apply H. reflexivity.
Qed.

(** One last thing: For partial maps, it's convenient to introduce a
    notion of map inclusion, stating that all the entries in one map
    are also present in another: *)

Definition includedin {A : Type} (m m' : map) :=
  forall (x : string) (v : A), m ? x = Some v -> m' ? x = Some v.


(** We can then show that map update preserves map inclusion -- that is: *)

Lemma includedin_update : forall (A : Type) (m m' : map)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold includedin.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq.
    + rewrite update_neq.
      * apply H.
      * apply Hxy.
    + apply Hxy.
Qed.

