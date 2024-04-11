From Coq Require Import Unicode.Utf8.
From Coq Require Import Strings.String.
Local Open Scope Z_scope.
Require Import ZArith.

(** TEST *)


Inductive type : Set :=
  (* Primitive types *)
  | Type_Unit : type
  | Type_Num : type
  | Type_Bool : type

  (* Functions *)
  | Type_Fun (t₁ t₂ : type) : type

  (* Product types *)
  | Type_Prod (t₁ t₂ : type) : type
  | Type_Recordt (l : lstype) : type

  (* Sum types *)
  | Type_Disjoint_Union (t₁ t₂ : type) : type
  | Type_Sum (name : string) : type
with 
  lstype :=
    | LST_Nil : lstype
    | LST_Cons (x : string) (t : type) (tail : lstype) : lstype
.



Inductive expr : Set := 
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
  | E_Recorde (bindings : lsexpr)
  | E_Record_Access (e : expr) (x : string)

  (* Recursion *)
  | E_Fix (e : expr)

  (* Sum types *)
  | E_In_Left (t₁ t₂ : type) (e : expr)
  | E_In_Right (t₁ t₂ : type) (e : expr)
  | E_Match (e case_left case_right : expr)

  | E_Unit 
  | E_Sum_Constr (constr : string) (e : expr)
  | E_Sum_Match (e default: expr) (branches : lsexpr)

  with 
    lsexpr : Set :=
    | LSE_Nil : lsexpr
    | LSE_Cons : string -> expr -> lsexpr -> lsexpr
.


Check expr_ind.
Scheme expr_mut_ind := Induction for expr Sort Prop
  with expr_list_ind := Induction for lsexpr Sort Prop
.
Check expr_mut_ind.



(* Record lookups *)
Fixpoint lookup_lstype (x : string) (l: lstype) : option type :=
  match l with 
  | LST_Nil => None 
  | LST_Cons name t tail =>
      if (name =? x)%string 
      then Some t 
      else lookup_lstype x tail
  end.

Fixpoint lookup_lsexpr (x : string) (l: lsexpr) : option expr :=
  match l with 
  | LSE_Nil => None 
  | LSE_Cons name t tail =>
      if (name =? x)%string 
      then Some t 
      else lookup_lsexpr x tail
  end.

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

  | V_Recordv :
      ∀ fields,
      value_lsexpr fields -> 
      value (E_Recorde fields)
  
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

Lemma lookup_lsexpr_value :
  ∀ (branches : lsexpr) (constr : string) (b : expr),
  value_lsexpr branches ->
  lookup_lsexpr constr branches = Some b -> 
  value b.
Proof.
  intros.
  induction branches. 
  - inversion H0.
  - inversion H; subst.
    simpl in *. destruct (String.eqb_spec s constr); subst; eauto.
    inversion H0; subst.
    assumption.
Qed.


Hint Constructors type : local_hints.
Hint Constructors expr : local_hints.
Hint Constructors lsexpr : local_hints.
Hint Constructors value : local_hints.
Hint Constructors value_lsexpr : local_hints.

Local Definition x := "x"%string.
Local Definition y := "y"%string.
Local Definition z := "z"%string.

Declare Custom Entry expr_ty.



Notation "'{{'  e  '}}'" := e (e custom expr_ty at level 99).


Notation " '`' x '`' " := x (in custom expr_ty at level 0, x constr at level 0).
Notation " '#' x " := x (in custom expr_ty at level 0, x constr at level 0).
Notation "x" := x (in custom expr_ty at level 0, x constr at level 0).
Notation "'Bool'" := Type_Bool (in custom expr_ty at level 0).
Notation "'Int'" := Type_Num (in custom expr_ty at level 0).
Notation "'Unit'" := Type_Unit (in custom expr_ty at level 0).
Notation "'(' t ')'" := t (in custom expr_ty at level 0).
Notation "t1 '->' t2" := (Type_Fun t1 t2) (in custom expr_ty at level 50, right associativity).
Notation "t1 '*' t2" := (Type_Prod t1 t2) (in custom expr_ty at level 30, left associativity).

Notation "t1 '+' t2" := (Type_Disjoint_Union t1 t2) (in custom expr_ty at level 40, left associativity).

Notation "'{'  t  '}'" := (Type_Recordt t) (in custom expr_ty at level 0, left associativity).


Notation "'Nil'" := 
  (LST_Nil)
  (in custom expr_ty at level 91).

Notation "l : t1 ; t2" := 
  (
    LST_Cons l t1 t2 
  ) (in custom expr_ty at level 98, right associativity).


Check {{ { #x : Int; #y : Bool; Nil} }}.


Declare Custom Entry expr.



(* Coercion E_Var : string >-> expr. *)




Notation "<{ e }>" := e (e custom expr at level 99).
Notation "( e )" := e (in custom expr, e at level 99).
Notation "{  e  }" := (E_Recorde e) (in custom expr, e at level 99).
Notation " '`' x '`' " := x (in custom expr at level 0, x constr at level 0).
Notation "x" := x (in custom expr at level 0, x constr at level 0).
Notation " # x" := (E_Var x) (in custom expr at level 0, x constr at level 0).
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
  (LSE_Nil)
  (in custom expr at level 91).

Notation "l := e1 ; e2" := 
  (
    LSE_Cons l e1 e2 
  ) (in custom expr at level 98, right associativity,
    format "l  ':='  e1  ';'  '/'  e2"
  ).

Notation "e '::' x" := (E_Record_Access e x)
  (in custom expr at level 90).

Notation "'fix' e" := 
  (E_Fix e)
  (
    in custom expr at level 90, 
    right associativity,
    format "'[v ' 'fix'  e ']'" 
  )
  .

Notation "'unit'" := E_Unit (in custom expr at level 90).

Notation "'inl' '<' t₁ | t₂ '>' e" := 
  (E_In_Left t₁ t₂ e) (
    in custom expr at level 90,
    t₁ custom expr_ty,
    t₂ custom expr_ty,
    e custom expr,
   right associativity).

Notation "'inr' '<' t₁ | t₂ '>' e" := 
  (E_In_Right t₁ t₂ e) (
    in custom expr at level 90,
    t₁ custom expr_ty,
    t₂ custom expr_ty,
    e custom expr,
   right associativity).


Notation "'match' e 'with' '|' 'inl' '=>' e_left '|' 'inr' '=>' e_right 'end'" :=
  (E_Match e e_left e_right)
  (
    in custom expr at level 90, 
    left associativity,
    format "'[v' 'match'  e  'with'  '/' '|'  'inl'  '=>'  e_left '/' '|'  'inr'  '=>'  e_right '/' 'end' ']'"
  )
  .

Notation "'match_sum' e 'with' lst ':' default 'end_sum'" :=
  (E_Sum_Match e default lst)
  (
    in custom expr at level 90, 
    left associativity,
    format "'[v' 'match_sum'  e  'with' '/' '[v'  lst ':' default  ']' '/' 'end_sum' ']'"

  )
  .
Check <{match 2 with | inl => 3 | inr => 4  end}>.
Check <{
    match_sum 2 with 
        `"Test"%string` := fun x : Bool => #x;
        `"Test2"%string` := fun x : Bool => #x;
        nil : true
     end_sum
}>.
Unset Printing Notations.
Set Printing Coercions.

Check <{
  {
    x := 3; nil
  }

}>.

Check <{
(fix
  let y = 4 in 
  (fun x : Bool * Bool + Int ->  {#x : Unit; Nil}  => 
  if #x 
  then first (2 - 1, (#y == 3, 4))
  else
     {y := 3; nil}::y) true)
      (match 2 with | inl => 3 | inr => 4  end )
      (match_sum 2 with `"Inl"%string` := 3 ; `"Inr"%string` := 4; nil : 4 end_sum )
}>.

