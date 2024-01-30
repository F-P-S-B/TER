From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Hints.

Inductive type :=
| Type_Num
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
| E_Num (z : Z)
| E_Minus (e1 e2 : expr)
.



Inductive value : expr -> Prop :=
| V_Num : ∀ z, value (E_Num z)
| V_True : value E_True
| V_False : value E_False
| V_Fun : 
    ∀ 
        (x : string) 
        (t : type) 
        (e : expr), 
    value (E_Fun x t e)
.

Hint Constructors type : local_hints.
Hint Constructors expr : local_hints.
Hint Constructors value : local_hints.
