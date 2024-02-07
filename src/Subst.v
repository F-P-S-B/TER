From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Closed.
Require Import Hints.

Require Maps.
Import Maps.Notations.
Require Import Syntax.
Require Import Types.

Inductive substitution (s : expr) (x : string) : expr -> expr -> Prop :=
  | S_Var_Eq :
      substitution s x (E_Var x) s
  | S_Var_Neq :
      ∀ (y : string), x <> y -> substitution s x (E_Var y) (E_Var y)
  | S_App : 
      ∀ (e1 e1' e2 e2' : expr),
      substitution s x e1 e1' ->
      substitution s x e2 e2' ->
      substitution s x (E_App e1 e2) (E_App e1' e2')
  | S_Fun_Eq : 
      ∀ (t : type) (e : expr),
      substitution s x (E_Fun x t e) (E_Fun x t e)
  | S_Fun_Neq : 
      ∀ (y: string) (t : type) (e e_aux e' : expr),
      x <> y ->
      closed s ->
      substitution s x e e' -> 
      substitution s x (E_Fun y t e) (E_Fun y t e')
  | S_True : 
      substitution s x E_True E_True
  | S_False : 
      substitution s x E_False E_False
  | S_If : 
      ∀ (e1 e1' e2 e2' e3 e3' : expr),
      substitution s x e1 e1' ->
      substitution s x e2 e2' ->
      substitution s x e3 e3' ->
      substitution s x (E_If e1 e2 e3) (E_If e1' e2' e3')
  | S_Let_Eq : 
      ∀ (e1 e1' e2 : expr),
      substitution s x e1 e1' -> 
      substitution s x (E_Let x e1 e2) (E_Let x e1' e2)
  | S_Let_Neq : 
      ∀ (y : string) (e1 e1' e2 e2': expr),
      x <> y ->
      closed s ->
      substitution s x e1 e1' -> 
      substitution s x e2 e2' -> 
      substitution s x (E_Let y e1 e2) (E_Let y e1' e2')
  
  | S_Num : 
      ∀ (z : Z),
      substitution s x (E_Num z) (E_Num z)
  | S_Minus :
      ∀ (e1 e1' e2 e2': expr),
      substitution s x e1 e1' -> 
      substitution s x e2 e2' -> 
      substitution s x (E_Minus e1 e2) (E_Minus e1' e2')
  | S_Pair : 
      ∀ (e1 e1' e2 e2': expr),
      substitution s x e1 e1' -> 
      substitution s x e2 e2' -> 
      substitution s x (E_Pair e1 e2) (E_Pair e1' e2')
  | S_First :
      ∀ (e e': expr),
      substitution s x e e' -> 
      substitution s x (E_First e) (E_First e')
  | S_Second :
      ∀ (e e': expr),
      substitution s x e e' -> 
      substitution s x (E_Second e) (E_Second e')

  | S_Record_Nil : 
      substitution s x E_Record_Nil E_Record_Nil
    
  | S_Record_Cons :
    ∀ y e e' tail tail',
    substitution s x tail tail' ->
    substitution s x e e' ->
    substitution s x (E_Record_Cons y e tail) (E_Record_Cons y e' tail')
  
  | S_Record_Access :
    ∀ y e e',
    substitution s x e e' ->
    substitution s x (E_Record_Access e y) (E_Record_Access e' y)
     
.

Hint Constructors substitution : local_hints.

Local Lemma exists_one : ∀ s x e, closed s -> ∃ e', 
substitution s x e e'.
Proof with eauto with local_hints.
  intros.
  induction e;
  try (try destruct IHe;
  try destruct IHe1;
  try destruct IHe2; 
  try destruct IHe3; 
  try destruct (String.eqb_spec x x0); 
  subst;
  eauto with local_hints; fail).
Qed.

Hint Resolve exists_one : local_hints.