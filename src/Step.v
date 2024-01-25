From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Syntax.
Require Import Subst.
Require Import Hints.

Inductive step : expr -> expr -> Prop := 
    | ST_App_Fun : 
        forall (x : string) (t : type) (e e' v : expr),
        value v -> 
        substitution v x e e' ->
        step (E_App (E_Fun x t e) v) e'
    | ST_App_Left : 
        forall (e1 e1' e2 : expr),
        step e1 e1' ->
        step (E_App e1 e2) (E_App e1' e2)
    | ST_App_Right : 
        forall (v1 e2 e2' : expr),
        value v1 ->
        step e2 e2' ->
        step (E_App v1 e2) (E_App v1 e2')
    | ST_If_True : 
        forall (e1 e2 : expr),
        step (E_If E_True e1 e2) e1
    | ST_If_False : 
        forall (e1 e2 : expr),
        step (E_If E_False e1 e2) e2
    | ST_If : 
        forall (e1 e1' e2 e3 : expr),
        step e1 e1' ->
        step (E_If e1 e2 e3) (E_If e1' e2 e3)
    | ST_Let_Left : 
        forall (x : string) (e1 e1' e2 : expr),
        step e1 e1' ->
        step (E_Let x e1 e2) (E_Let x e1' e2)
    | ST_Let_Right : 
        forall (x : string) (v1 e2 e2' : expr),
        value v1 ->
        substitution v1 x e2 e2' ->
        step (E_Let x v1 e2) e2'
    | ST_Minus_Left :  
        forall (e1 e1' e2 : expr),
        step e1 e1' ->
        step (E_Minus e1 e2) (E_Minus e1' e2)
    | ST_Minus_Right :  
        forall (v1 e2 e2' : expr),
        value v1 ->
        step e2 e2' ->
        step (E_Minus v1 e2) (E_Minus v1 e2')
    | ST_Minus_Num : 
        forall (z1 z2 : Z),
        step 
            (E_Minus (E_Num z1) (E_Num z2))
            (E_Num (z1 - z2))
.

Hint Constructors step : local_hints.
