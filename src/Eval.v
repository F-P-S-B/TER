From Coq Require Import Unicode.Utf8.
Require Import Types.
Require Import Syntax.
Require Import Step.
Require Import Subst.
Require Import Hints.
Require Import Closed.
Local Open Scope Z_scope.
Require Import ZArith.
Require Import Lia.
Require Import String.
Require Import Multi.
(* TODO éventuellement: lien avec multistep *)

Fixpoint sub (s : expr) (x : string) (e: expr) := 
  match e with 
  | E_Var v => if (x =? v)%string then s else E_Var v

  | <{ e₁ e₂}> => 
      let e₁ := sub s x e₁ in
      let e₂ := sub s x e₂ in
      <{e₁ e₂}>

  | <{fun v : t => e}> => 
      let e :=
        if (x =? v)%string 
        then e
        else sub s x e 
      in
      <{fun v : t => e}>

  | <{true}> => <{true}>

  | <{false}> => <{false}>

  | <{if e₁ then e₂ else e₃}> => 
      let e₁ := sub s x e₁ in
      let e₂ := sub s x e₂ in
      let e₃ := sub s x e₃ in
      <{if e₁ then e₂ else e₃}>

  | <{let v = e₁ in e₂}> =>
      let e₁ := sub s x e₁ in
      let e₂ :=
        if (x =? v)%string 
        then e₂
        else sub s x e₂  in
      <{let v = e₁ in e₂}>

  | E_Num z => E_Num z

  | <{ e₁ - e₂}> => 
      let e₁ := sub s x e₁ in
      let e₂ := sub s x e₂ in
      <{e₁ - e₂}>

  | <{ e₁ == e₂}> => 
      let e₁ := sub s x e₁ in
      let e₂ := sub s x e₂ in
      <{e₁ == e₂}>

  | <{(e₁, e₂)}> =>
      let e₁ := sub s x e₁ in
      let e₂ := sub s x e₂ in
      <{(e₁, e₂)}>

  | <{first e}> => 
      let e := sub s x e in
      <{first e}>

  | <{second e}> => 
      let e := sub s x e in
      <{second e}>

  | <{nil}> => <{nil}>

  | <{ v := e; etail}> => 
      let e := sub s x e in
      let etail := sub s x etail in
      <{ v := e; etail}>
  | <{e::v}> =>
      let e := sub s x e in
      <{e :: v}>
  | <{fix e}> =>
      let e := sub s x e in
      <{fix e}>

  | E_In_Left t₁ t₂ e => E_In_Left t₁ t₂ (sub s x e)
  | E_In_Right t₁ t₂ e => E_In_Right t₁ t₂ (sub s x e)
  | E_Match e e_left e_right => E_Match (sub s x e) (sub s x e_left) (sub s x e_right)
  | E_Unit => E_Unit
  | E_Sum_Constr constr e => E_Sum_Constr constr (sub s x e)
  end.

Inductive result {A B} := 
  | Ok : A -> result 
  | Err : B ->  result
. 
Fixpoint eval_aux (n : nat) (e : expr) : @result expr string   := 
  match n with 
  | O => Err "Maximum recursion depth reached"%string
  | S n => 
    match e with 
    | E_Var x => Err ("Unbound variable" ++ x)%string 
    | <{ e₁ e₂}> => 
      match eval_aux n e₁ with 
      | Ok <{fun x : t => e}> => eval_aux n (sub e₂ x e)
      | Ok _ => Err "Non-functional appplication"%string
      | e => e
      end
    | <{fun x : t => e}> => Ok <{fun x : t => e}>
    | <{true}> => Ok <{true}>
    | <{false}> => Ok <{false}>
    | <{if e₁ then e₂ else e₃}> => 
      match eval_aux n e₁ with 
      | Ok <{true}> => eval_aux n e₂
      | Ok <{false}> => eval_aux n e₃
      | Ok _ => Err "Non-boolean If condition"%string
      | err => err
      end
    | <{let x = e₁ in e₂}> => eval_aux n (sub e₁ x e₂)
    | E_Num z => Ok (E_Num z)
    | <{ e₁ - e₂}> => 
      match eval_aux n e₁, eval_aux n e₂ with 
      | Ok (E_Num z₁), Ok (E_Num z₂) => Ok (E_Num (z₁ - z₂))
      | Ok _, Ok _ => Err "Non Numeric substraction"%string
      | Err e, _ | _, Err e => Err e
      end
    | <{ e₁ == e₂}> => 
      match eval_aux n e₁, eval_aux n e₂ with 
      | Ok (E_Num z₁), Ok (E_Num z₂) => Ok (
        if z₁ =? z₂ then <{true}> else <{false}>
      )
      | Ok _, Ok _ => Err "Non Numeric comparison"%string
      | Err e, _ | _, Err e => Err e
      end

    | <{(e₁, e₂)}> =>
      match eval_aux n e₁, eval_aux n e₂ with 
      | Ok e₁, Ok e₂ => Ok <{(e₁, e₂)}>
      | Err e, _  | _, Err e => Err e
      end

  | <{first e}> => 
      match eval_aux n e with 
      | Ok <{ (e₁, _) }> => Ok e₁
      | Ok _ => Err "Non pair projection first"%string
      | e => e
      end

  | <{second e}> => 
      match eval_aux n e with 
      | Ok <{ (_, e₂) }> => Ok e₂
      | Ok _ => Err "Non pair projection second"%string
      | e => e
      end

  | <{nil}> => Ok <{nil}>

  | <{ x := e; etail}> => 
      match eval_aux n e, eval_aux n etail with 
      | Ok e, Ok etail => Ok <{ x := e; etail}>
      | Err e, _ | _, Err e => Err e
      end 
  | <{e::x}> =>
      match eval_aux n e with 
      | Ok e => 
        match lookup_val_record x e with 
        | Some e => Ok e 
        | None =>  Err ("Access to unbound field " ++ x ++ " or to a non-record value")%string
        end
      | err => err
      end
  | <{fix e}> =>
      match eval_aux n e with 
      | Ok <{fun x : t => e}> => 
        let e := sub <{fix <{fun x : t => e}>}> x e in 
        Ok e
      | err => err 
      end
  | E_In_Left t₁ t₂ e =>
      match eval_aux n e with 
      | Ok e => Ok (E_In_Left t₁ t₂ e)
      | err => err
      end
  | E_In_Right t₁ t₂ e =>
      match eval_aux n e with 
      | Ok e => Ok (E_In_Right t₁ t₂ e)
      | err => err
      end
  | E_Match e e_left e_right =>
      match eval_aux n e with 
      | Ok (E_In_Left _ _ e) => eval_aux n (E_App e_left e)
      | Ok (E_In_Right _ _ e) => eval_aux n (E_App e_right e)
      | err => err
      end
  | E_Unit => Ok E_Unit
  | E_Sum_Constr constr e =>
    match eval_aux n e with 
    | Ok e' => Ok (E_Sum_Constr constr e')
    | err => err
    end
  end
end.

Definition eval := eval_aux (5001)%nat. 


Definition eq := "eq"%string.
Definition m := "m"%string.
Definition n := "n"%string.

Compute eval <{
  let eq = fix
    fun eq : (Type_Num -> Type_Num -> Type_Bool) =>
      fun m : Type_Num => 
        fun n : Type_Num => 
          if m == 0
          then n == 0 
          else 
            if n == 0 
            then false 
            else  
              eq (n-1) (m-1)
  in 
  let n = 10 in 
  let m = 10 in 
  eq n m
}>.



Definition add := 
  let n := "n"%string in 
  let m := "m"%string in 
  <{fun n : Type_Num => fun m : Type_Num => n - (0 - m)}>.


Definition mul := 
  let n := "n"%string in 
  let m := "m"%string in 
  let mul := "mul"%string in 
  <{
    fix 
      fun mul : Type_Num -> Type_Num -> Type_Num => 
      fun n : Type_Num =>
      fun m : Type_Num =>
        if n == 0 
        then 0 
        else add m (mul m (n - 1))
  }>.

Definition fact := 
  let fact := "fact"%string in 
  <{
    fix 
      fun fact : Type_Num -> Type_Num =>
      fun n : Type_Num => 
      if n == 0 then 1 
      else mul n (fact (n-1))
  }>

.


Compute eval <{fact 5}>.

Definition div2 :=
  let div2 := "div2"%string in 
 <{
  fix 
    fun div2 : Type_Num -> Type_Num -> Type_Num =>
    fun n : Type_Num => 
    if n == 0 then 0 
    else 
      if n == 1
      then 0 
      else add 1 (div2 (n - 2))
 }>.


Definition sumrec := 
  let sumrec := "sumrec"%string in 
  <{
    fix 
      fun sumrec : Type_Num -> Type_Num =>
      fun n : Type_Num =>
      if n == 0 then 0 
      else add n (sumrec (n - 1)) 
  }>
  .

Definition sumcalc := 
  let sumcalc := "sumcalc"%string in 
  <{
    fun n : Type_Num => div2 (mul n (add n 1)) 
  }>.
Compute eval <{
  sumcalc 18 == sumrec 18
}>.


Theorem substitution_sub :
  ∀ s x e e',
  closed s ->
  substitution s x e e' <->
  sub s x e = e'.
Proof with eauto with local_hints.
  split.
  {
  generalize dependent s; 
  generalize dependent x; 
  generalize dependent e'.
  induction e; intros * H_closed H_subst; 
  try 
  (
    simpl;
    inversion H_subst; subst;
    try apply IHe in H0;
    try apply IHe in H2;
    try apply IHe1 in H1;
    try apply IHe2 in H3;
    try apply IHe1 in H4;
    try apply IHe2 in H3;
    subst;
    eauto with local_hints;
    fail
  ).
  - simpl. destruct (String.eqb_spec x0 x); 
    inversion H_subst; subst;
    eauto; exfalso...
  - simpl. destruct (String.eqb_spec x0 x); 
    inversion H_subst; subst; 
    try (exfalso; eauto with local_hints; fail)...
    apply IHe in H5; subst...
  - simpl.
    inversion H_subst; subst.
    apply IHe1 in H2;
    apply IHe2 in H4;
    apply IHe3 in H5;
    subst;
    eauto with local_hints.
  - simpl. 
    simpl. destruct (String.eqb_spec x0 x); 
    inversion H_subst; subst;
    try (exfalso; eauto with local_hints; fail)...
    apply IHe1 in H3; subst...
    apply IHe1 in H5; apply IHe2 in H6; subst...
  - simpl. inversion H_subst; subst. erewrite IHe.
    + reflexivity.
    + assumption.
    + assumption.  
  - simpl. inversion H_subst; subst. erewrite IHe.
    + reflexivity.
    + assumption.
    + assumption. 
  - simpl. inversion H_subst; subst. 
    erewrite IHe1; try erewrite IHe2; try erewrite IHe3; auto.
  }
  {
  generalize dependent s; 
  generalize dependent x; 
  generalize dependent e'.
  induction e; intros * H_closed H_subst;
  simpl in H_subst;
  try (
      try destruct (String.eqb_spec x0 x); 
      inversion H_subst; subst; 
      eauto with local_hints; fail
  ).
  }
Qed.

Theorem eval_value :
  ∀ e e' n,
  eval_aux n e = Ok e' ->
  value e'.
Proof.
  intros e.
  induction e; intros e' n H_eval; destruct n;
  try (inversion H_eval; fail); simpl in H_eval.
  - destruct (eval_aux n0 e1);
    try destruct e; try (inversion H_eval; fail).
  (* Faux, il faut bien typer *)
    

Admitted.

Theorem eval_multistep :
  ∀ Σ e t e' n, 
  has_type Σ empty e t ->
  eval_aux n e = Ok e' ->
  e -->* e'.
Proof with eauto with local_hints.
  induction e; intros.
  - destruct n0;
    inversion H0.
  - destruct n0. inversion H0.
    simpl in H0.
    destruct (eval_aux n0 e1).
    + destruct e; try (inversion H0; fail).
      inversion H; subst.
    
      

Admitted.

