From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Maps.
Import Maps.Notations.
Require Import Hints.

Inductive type :=
| Type_Num
| Type_Bool
| Type_Fun (t₁ t₂ : type)
| Type_Prod (t₁ t₂ : type)
.


Inductive expr := 
| E_Var (x : string) 
| E_App (e1 e2 : expr) 
| E_Fun (x : string) (t : type) (e : expr) 
| E_True  
| E_False 
| E_If (e1 e2 e3 : expr)  
| E_Let (x : string) (e1 e2 : expr)
| E_Num (z : Z)
| E_Minus (e1 e2 : expr)
| E_Pair (e1 e2 : expr)
| E_First (e : expr) 
| E_Second (e : expr) 
.
(* TODO: Adapter les defs, notamment Subst *)

(* 
  Les records sont des map `nom du champ -> expr`
  Une paire de type A × B peut être représentée comme un record { first : A, second : B }
*)



Inductive value : expr -> Prop :=
| V_True : value E_True
| V_False : value E_False
| V_Fun : 
    ∀ x t e, 
    value (E_Fun x t e)
| V_Num : ∀ z, value (E_Num z)
| V_Pair :
  ∀ e1 e2, 
  value e1 ->
  value e2 -> 
  value (E_Pair e1 e2)
.

Hint Constructors type : local_hints.
Hint Constructors expr : local_hints.
Hint Constructors value : local_hints.
