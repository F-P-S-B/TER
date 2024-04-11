From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.
Require Maps.
Import Maps.Notations.
Require Import Hints.

Inductive type :=
  (* Primitive types *)
  | Type_Unit
  | Type_Num
  | Type_Bool

  (* Functions *)
  | Type_Fun (t₁ t₂ : type)

  (* Product tyoes *)
  | Type_Prod (t₁ t₂ : type)
  | Type_Record_Nil
  | Type_Record_Cons (x : string) (t₁ t₂ : type)

  (* Sum types *)
  | Type_Disjoint_Union (t₁ t₂ : type)

  | Type_Sum (name : string)

.



Inductive record_type : type -> Prop :=
  | RT_Nil : 
      record_type Type_Record_Nil
  | RT_Cons :
      ∀ x t₁ t₂, 
      record_type t₂ -> 
      record_type (Type_Record_Cons x t₁ t₂)
.

Hint Constructors record_type : local_hints.


Inductive exception :=
  | Ex_Unhandled_Case
.
Hint Constructors exception : local_hints.

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

  (* Sum types *)
  | E_In_Left (t₁ t₂ : type) (e : expr)
  | E_In_Right (t₁ t₂ : type) (e : expr)

  | E_Match (e case_left case_right : expr)

  | E_Unit 
  | E_Sum_Constr (constr : string) (e : expr)

  | E_Sum_Match (e : expr) (branches : lsexpr)
  (* 
    Ajouter Exceptions:
      - err: Unhandled branch
    Pour typer:
    - vérifier l'inclusion mais pas l'exhaustivité
    Pour step:
    - Si inclus: Comme Match inl/inr
    - Si non inclus: exception Ex_Unhandled_Case
    
    Pour step les exception: faire 
  *)

  | E_Exception (e: exception)
  with 
    lsexpr :=
    | LSE_Nil : lsexpr
    | LSE_Cons : string -> expr -> lsexpr -> lsexpr
.

Fixpoint In_LSE (e: expr) (l: lsexpr) : Prop :=
    match l with
      | LSE_Nil => False
      | LSE_Cons _ h t => h = e \/ In_LSE e t
    end.

(* Type branches, induction mutuelle, en déduire un meilleur principe de récurrence *)

Check expr_ind.


Scheme expr_mut_ind := Induction for expr Sort Prop
  with expr_list_ind := Induction for lsexpr Sort Prop.
  Check expr_mut_ind.
(* 
  Pour généraliser: 
  Element Constructeur, identifier avec numéro

  Environnement lie numéro constructeur -> type constructeur

  Découper proprement en 2 environnements

  Environnement devient paire Environnement constructeurs, Environnement variables


  Todo éventuellement:
  Traduction avec Inl, Inr vers Type sum générique


*)

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





Local Lemma lookup_type_record_some_is_record : 
  ∀ x t v, 
  lookup_type_record x t = Some v -> 
  ∃ y t₁ t₂, t = Type_Record_Cons y t₁ t₂.
Proof.
  intros.
  induction t;
  try (inversion H; fail).
  eauto.
Qed. 


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
      value (E_Record_Nil)

  | V_Record_Cons :
      ∀ x e tail,
      value e -> 
      value tail -> 
      value (E_Record_Cons x e tail)
  
  | V_In_Left :
      ∀ e t₁ t₂, 
      value e -> 
      value (E_In_Left t₁ t₂ e) 

  | V_In_Right :
      ∀ e t₁ t₂, 
      value e -> 
      value (E_In_Right t₁ t₂ e) 

  | V_Unit :
      value E_Unit

  | V_Sum_Constr : 
      ∀ constr e,
      value e ->
      value (E_Sum_Constr constr e)
with value_lsexpr : lsexpr -> Prop :=
  | V_LSExpr_Nil : value_lsexpr LSE_Nil
  | V_LSExpr_Cons :
    ∀ e branches constr,
      value e ->
      value_lsexpr branches ->
      value_lsexpr (LSE_Cons constr e branches)
.


Inductive blocking_expr : expr -> Prop := 
  | BE_Exc : ∀ e : exception, blocking_expr (E_Exception e)
  | BE_Val : ∀ e : expr, value e -> blocking_expr e
.

Inductive blocking_lsexpr : lsexpr -> Prop :=
  | BLSE_Val : ∀ branches, value_lsexpr branches -> blocking_lsexpr branches
  .

Hint Constructors type : local_hints.
Hint Constructors expr : local_hints.
Hint Constructors lsexpr : local_hints.
Hint Constructors value : local_hints.
Hint Constructors value_lsexpr : local_hints.

(* TODO: revoir priorités *)
Definition x := "x"%string.
Definition y := "y"%string.
Definition z := "z"%string.

Declare Custom Entry expr_ty.

Notation "'{{' e '}}'" := e (e custom expr_ty at level 99).


Notation "x" := x (in custom expr_ty at level 0, x constr at level 0).
Notation "'Bool'" := Type_Bool (in custom expr_ty at level 0).
Notation "'Int'" := Type_Num (in custom expr_ty at level 0).
Notation "'Unit'" := Type_Unit (in custom expr_ty at level 0).
Notation "'(' t ')'" := t (in custom expr_ty at level 0).
Notation "t1 '->' t2" := (Type_Fun t1 t2) (in custom expr_ty at level 50, right associativity).
Notation "t1 '*' t2" := (Type_Prod t1 t2) (in custom expr_ty at level 30, left associativity).

Notation "t1 '+' t2" := (Type_Disjoint_Union t1 t2) (in custom expr_ty at level 40, left associativity).


Notation "'nil'" := (Type_Record_Nil) (in custom expr_ty).
Notation " x ':' t1  '::' t2" := (Type_Record_Cons x t1 t2) (
  in custom expr_ty at level 1,
  left associativity).


Check {{ Bool + x : Bool :: nil }}.


Declare Custom Entry expr.



Coercion E_Var : string >-> expr.




Notation "<{ e }>" := e 
  (
    e custom expr at level 99
  ).
Notation "( e )" := e (in custom expr, e at level 99).
(* Notation "{ e }" := e (in custom expr, e at level 99). *)
Notation " '`' x '`' " := x (in custom expr at level 0, x constr at level 0).
Notation "x" := x (in custom expr at level 0, x constr at level 0).
Notation "x y" := 
  (E_App x y) (in custom expr at level 1, left associativity).

Notation "'fun' x ':' t '=>' e" :=
  (E_Fun x t e) 
  (
    in custom expr at level 90, 
    x at level 99,
    t custom expr_ty at level 99,
    e custom expr at level 99,
    no associativity,
    format "'[v ' 'fun'  x  ':'  t  '=>'  e ']'"
  ).
Notation "'true'"  := true (at level 1).
Notation "'true'" := E_True (in custom expr at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'" := E_False (in custom expr at level 0).
Notation "'if' e1 'then' e2 'else' e3" := 
  (E_If e1 e2 e3) 
  (in custom expr at level 89,  
    e1 custom expr at level 99,
    e2 custom expr at level 99,
    e3 custom expr at level 99,
    left associativity,
    format "'[v ' 'if'  e1 '/' '[hv' 'then'  e2 ']' '/' '[hv' 'else'  e3 ']' ']'"
    ).

Notation "'let' x '=' e1 'in' e2" := 
  (E_Let x e1 e2)
  (in custom expr at level 89,  
    e1 custom expr at level 99,
    e2 custom expr at level 99,
    left associativity,
    format "'[ ' 'let'  x  '='  e1  'in'  '/' e2 ']'"
    
    ).

Coercion E_Num : Z >-> expr.

Notation "e1 '-' e2" := 
  (E_Minus e1 e2)
  (in custom expr at level 91,  
    (* e1 custom expr at level 99, *)
    e2 custom expr at level 99,
    left associativity).
Notation "e1 '==' e2" := 
  (E_Eq e1 e2)
  (in custom expr at level 92,  
    (* e1 custom expr at level 99, *)
    e2 custom expr at level 99,
    left associativity).

Notation "'(' e1 ',' e2 ')'" := 
  (E_Pair e1 e2)
  (in custom expr at level 0,
  e1 custom expr at level 99,
  e2 custom expr at level 99,
  right associativity).

Notation "'first' e" := 
  (E_First e)
  (in custom expr at level 91).

Notation "'second' e" := 
  (E_Second e)
  (in custom expr at level 91).

Notation "'nil'" := 
  (E_Record_Nil)
  (in custom expr at level 91).

Notation "e '::' x" := (E_Record_Access e x)
  (in custom expr at level 90).

Notation "l := e1 ; e2" := 
  (
    E_Record_Cons l e1 e2 
  ) (in custom expr at level 98, right associativity).

Notation "'fix' e" := 
  (E_Fix e)
  (
    in custom expr at level 90, 
    right associativity,
    format "'[v ' 'fix'  e ']'" 
  )
  .


Notation "'Inl' t₁ t₂ e" := 
  (E_In_Left t₁ t₂ e)
  (in custom expr at level 90, right associativity).

Notation "'Inr' t₁ t₂ e" := 
  (E_In_Right t₁ t₂ e)
  (in custom expr at level 90, right associativity).


Notation "'match' e 'with' '|' 'Inl' '=>' e_left '|' 'Inr' '=>' e_right 'end'" :=
  (E_Match e e_left e_right)
  (
    in custom expr at level 90, 
    left associativity,
    format "'[v' 'match'  e  'with'  '/' '|'  'Inl'  '=>'  e_left '/' '|'  'Inr'  '=>'  e_right '/' 'end' ']'"
  )
  .

  Check <{match 2 with | Inl => 3 | Inr => 4  end}>.
(* Unset Printing Notations. *)
Set Printing Coercions.


Check <{
  
(fix
  let y = 4 in 
  (fun x : Type_Bool * Type_Bool + Type_Num ->  x : Type_Unit ::nil  => 
  if x 
  then first (2 - 1, (y == 3, 4))
  else
     (y := 3; nil)::y) true)
      (match 2 with | Inl => 3 | Inr => 4  end )
}>.


Check expr_mut_ind.
