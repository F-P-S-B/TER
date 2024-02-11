From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Maps.
Import Maps.Notations.
Require Import Hints.

Inductive type :=
  (* Primitive types *)
  | Type_Num
  | Type_Bool

  (* Composed types *)
  | Type_Fun (t₁ t₂ : type)
  | Type_Prod (t₁ t₂ : type)
  | Type_Record_Nil 
  | Type_Record_Cons (x : string) (t₁ t₂ : type)
.


Inductive record_type : type -> Prop :=
  | RT_Nil : 
      record_type Type_Record_Nil
  | RT_Cons :
      ∀ x t₁ t₂, 
      record_type t₂ -> 
      record_type (Type_Record_Cons x t₁ t₂)
.

Inductive expr := 
  (* Lambda calculus *)
  | E_Var (x : string) 
  | E_App (e1 e2 : expr) 
  | E_Fun (x : string) (t : type) (e : expr) 

  (* Booleans and conditions *)
  | E_True  
  | E_False 
  | E_If (e1 e2 e3 : expr)  

  (* Let expressions *)
  | E_Let (x : string) (e1 e2 : expr)

  (* Arithmetic *)
  | E_Num (z : Z)
  | E_Minus (e1 e2 : expr)
  | E_Eq (e1 e2 : expr)

  (* Pairs *)
  | E_Pair (e1 e2 : expr)
  | E_First (e : expr) 
  | E_Second (e : expr) 

  (* Records *)
  | E_Record_Nil
  | E_Record_Cons (x : string) (e tail : expr)
  | E_Record_Access (e : expr) (x : string)

  (* Recursion *)
  | E_Fix (e : expr)
.

(* Record lookups *)
Fixpoint lookup_type_record (x : string) (t: type) :=
  match t with 
  | Type_Record_Cons y t t_tail =>
    if String.eqb x y then Some t else lookup_type_record x t_tail
  | _ => None 
  end.

Fixpoint lookup_val_record (x : string) (e: expr) :=
  match e with 
  | E_Record_Cons y v tail =>
    if String.eqb x y then Some v else lookup_val_record x tail
  | _ => None 
  end.

(* Local Lemma lookup_type_record_some_is_record : 
  ∀ x t v, 
  lookup_type_record x t = Some v -> 
  ∃ y t₁ t₂, t = Type_Record_Cons y t₁ t₂.
Proof.
  intros.
  induction t;
  try (inversion H; fail).
  eauto.
Qed.  *)


Inductive value : expr -> Prop :=
  | V_True : 
      value E_True
  | V_False : 
      value E_False
  | V_Fun : 
      ∀ x t e, 
      value (E_Fun x t e)
  | V_Num : 
      ∀ z, value (E_Num z)
  | V_Pair :
      ∀ e1 e2, 
      value e1 ->
      value e2 -> 
      value (E_Pair e1 e2)

  | V_Record_Nil : 
      value E_Record_Nil

  | V_Record_Cons :
      ∀ x e tail,
      value e -> 
      value tail -> 
      value (E_Record_Cons x e tail)
.

Hint Constructors type : local_hints.
Hint Constructors expr : local_hints.
Hint Constructors value : local_hints.
