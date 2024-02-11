From Coq Require Import Unicode.Utf8.
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
Require Import Hints.
Set Default Goal Selector "!".


Inductive map {A} :=
  | empty
  | update (m : map) (key : string) (val : A) 
.


Fixpoint find {A} (m : map) (key : string) : option A :=
  match m with 
  | empty => None 
  | update m k v => 
      if (k =? key)%string 
      then Some v 
      else find m key
  end.


Module Notations.
(** We introduce a similar notation for partial maps: *)
  Notation "x '|->' v ';' m" := (update m x v)
    (at level 100, v at next level, right associativity).

  (** We can also hide the last case when it is empty. *)
  Notation "x '|->' v" := (update empty x v)
    (at level 100).

  Notation "m '?' x" := (find m x)
    (at level 50, left associativity).
End Notations.

Import Notations.

Axiom Maps_extensionnality :
 ∀ A (m1 m2 : @map A), 
 (∀ x, m1 ? x = m2 ? x) -> 
 m1 = m2.




Lemma apply_empty : ∀ (A : Type) (x : string),
  (@empty A) ? x = None.
Proof.
  auto.
Qed.



Lemma update_eq : 
  ∀ (A : Type) (m : map) (x: string) (v: A),
  (x |-> v; m) ? x = Some v.
Proof. 
  intros. 
  simpl.
  rewrite String.eqb_refl.
  reflexivity.
Qed.




Theorem update_neq : 
  ∀ (A : Type) (m : map) (x1 x2 : string) (v : A),
  x2 <> x1 ->
  (x2 |-> v; m) ? x1 = m ? x1.
Proof.
  intros A m x1 x2 v H.
  rewrite <- String.eqb_neq in H.
  simpl. rewrite H.
  reflexivity.
Qed.




Lemma update_shadow : ∀ (A : Type) (m : map) (x : string) (v1 v2 : A),
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m x v1 v2. 
  apply Maps_extensionnality. intro y. simpl.
  destruct (String.eqb_spec x y); reflexivity.
Qed.




Theorem update_same :
  ∀ (A : Type) (m : map) (x : string) (v : A),
  m ? x = Some v ->
  (x |-> v; m) = m .
Proof.
  intros A m x v H. apply Maps_extensionnality. intro y. simpl. rewrite <- H.
  destruct (String.eqb_spec x y); subst; reflexivity.
Qed.




Theorem update_permute : 
  ∀ (A : Type) (m : map) 
    (x1 x2 : string) (v1 v2 : A),
  x2 <> x1 ->
  (x2 |-> v2; x1 |-> v1; m) = (x1 |-> v1; x2 |-> v2; m).
Proof.
  intros A m x1 x2 v1 v2 H.
  apply Maps_extensionnality. intro y.
  simpl.
  destruct (String.eqb_spec x1 y);
  destruct (String.eqb_spec x2 y); subst; auto.
  exfalso. apply H. reflexivity.
Qed.




Definition includedin {A : Type} (m m' : map) :=
  ∀ (x : string) (v : A), 
  m ? x = Some v -> m' ? x = Some v.





Lemma includedin_update : 
  ∀ (A : Type) (m m' : map) (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx; m) (x |-> vx; m').
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



Lemma includedin_refl : 
  ∀ (A : Type) m, @includedin A m m.
Proof.
  intros.
  induction m.
  - intros x v H. inversion H.
  - apply includedin_update. assumption.
Qed.


(* Definition same_bindings {A B : Type} (m₁ : @map A) (m₂ : @map B) :=
  ∀ x,
 (∃ v₁, m₁ ? x = Some v₁) <-> (∃ v₂, m₂ ? x = Some v₂).

Example ex1 :
  ∀ x, 
  same_bindings (x |-> 1) (x |-> "a"%string).
Proof.
  intros x x'.
  split.
  - intros [v₁ H]. 
    destruct (String.eqb_spec x x').
    + subst. 
      exists "a"%string.
      simpl. rewrite String.eqb_refl.
      reflexivity. 
    + rewrite update_neq in H; auto. inversion H. 
  - intros [v₁ H].
    destruct (String.eqb_spec x x').
    + subst. eexists. unfold find. rewrite String.eqb_refl. reflexivity.
    + rewrite update_neq in H. 
      * inversion H.
      * assumption.
Qed.

Theorem same_bindings_update :
  ∀ (A B : Type) (m m' : map) (x : string) (va : A) (vb : B),
  same_bindings m m' ->
  same_bindings (x |-> va; m) (x |-> vb; m').
Proof.
  intros.
  unfold same_bindings.
  intros x'.
  unfold same_bindings in H.
  specialize H with x'.
  split;
  intros [v H_v];
  destruct (String.eqb_spec x x');
  try (subst; eexists; rewrite update_eq; reflexivity);
  rewrite update_neq in H_v; auto;
  rewrite update_neq; eauto;
  try rewrite <- H; eauto;
  try rewrite H; eauto.
Qed.
       

Lemma same_bindings_empty : 
  ∀ (A B : Type) m,
  @same_bindings A B empty m -> 
  m = empty.
Proof.
  intros A B.
  induction m; intro H_same; auto.
  assert (H_same' := H_same).
  unfold same_bindings in H_same. 
  specialize H_same with key as [H1 H2].
  apply Maps_extensionnality.
  intro.
  destruct (String.eqb_spec key x).
  - subst.
    assert (∃ v₁ : A, empty ? x = Some v₁).
    {
      apply H2.
      eexists. simpl.
      rewrite String.eqb_refl. 
      reflexivity.
    }
    inversion H.
    inversion H0.
  - assert (∃ v₁ : A, empty ? x = Some v₁).
    {
      apply H2.
      eexists. simpl.
      rewrite String.eqb_refl. 
      reflexivity.
    }
    inversion H.
    inversion H0.
Qed.
  

Lemma same_bindings_empty_empty : 
  ∀ (A B : Type), @same_bindings A B empty empty.
Proof.
  intros.
  unfold same_bindings. intro.
  split; 
  intros [v H_contra]; 
  inversion H_contra.
Qed.

Theorem same_bindings_refl :
  ∀ (A : Type) m, @same_bindings A A m m.
Proof.
  intros.
  induction m.
  - intros x. split; auto.
  - apply same_bindings_update. assumption.
Qed. 

Theorem same_bindings_sym :
  ∀ (A B: Type) (m1 : @map A) (m2 : @map B), 
  same_bindings m1 m2 -> 
  same_bindings m2 m1.
Proof.
  intros.
  unfold same_bindings in *.
  split; intro.
  - rewrite H. assumption.
  - rewrite <- H. assumption.
Qed.


Theorem same_bindings_trans :
  ∀ (A B C : Type) (m1 : @map A) (m2 : @map B) (m3 : @map C),
  same_bindings m1 m2 -> 
  same_bindings m2 m3 -> 
  same_bindings m1 m3.
Proof.
  intros.
  unfold same_bindings in *.
  split; intro.
  - rewrite <- H0.
    rewrite <- H.
    assumption.
  - rewrite H.
    rewrite H0.
    assumption.
Qed.

Theorem same_bindings_shadow_add :
  ∀ (A B : Type) (m1 : @map A ) (m2 : @map B) x (v v' : A), 
  same_bindings m1 m2 ->  
  m1 ? x = Some v ->
  same_bindings (x |-> v'; m1) m2.
Proof.
  intros A B.
  induction m1; intros m2 x v v' H_same_bindings H_m1_x.
  - apply same_bindings_empty in H_same_bindings. inversion H_m1_x. 
  - unfold same_bindings in H_same_bindings.
    unfold same_bindings. intro.
    split; intro.
    + rewrite <- H_same_bindings.
      destruct (String.eqb_spec x0 x).
      * subst. eexists. eassumption.
      * rewrite update_neq in H; eauto.
    + destruct (String.eqb_spec x0 x).
      * subst. simpl. rewrite String.eqb_refl. eauto.
      * rewrite update_neq; eauto.  
        rewrite H_same_bindings. eauto. 
Qed. *)

      




