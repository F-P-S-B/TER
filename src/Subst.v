From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Syntax.
Require Import Hints.

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
    | S_Num : 
        forall (z : Z),
        substitution s x (E_Num z) (E_Num z)
    | S_Minus :
        forall (e1 e1' e2 e2': expr),
        substitution s x e1 e1' -> 
        substitution s x e2 e2' -> 
        substitution s x (E_Minus e1 e2) (E_Minus e1' e2')
.

Hint Constructors substitution : local_hints.

Local Lemma exists_one : ∀ s x e, ∃ e', substitution s x e e'.
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

Hint Resolve exists_one : local_hints.