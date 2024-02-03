(*****************************************************************)
(******                       M2 LMFI                      *******)
(******   Functional programming and formal proofs in Coq  *******)
(****** Project : compiling expressions with sums          *******)
(******            designed by Pierre Letouzey             *******)
(*****************************************************************)

Require Import String Datatypes Arith List Lia.
Import ListNotations.
Open Scope nat_scope.

(** What you should do :
    a) Remove axiom TODO  and replace its uses by working code.
    b) Replace all uses of  Admitted by actual proofs. *)

(** I) Library *)

(** Compararing integers

    In Coq, comparing a <= b is a logical statement (that is
    a term in Prop). One cannot use it as a test in a
    program. To do so, one shall use boolean comparison
    a <=? b (corresponding to constant Nat.leb).
    Here is the link between the two notions,  *)

Lemma leb_le x y : (x <=? y) = true <-> x <= y.
Proof.
 apply Nat.leb_le.
Qed.

Lemma leb_gt x y : (x <=? y) = false <-> y < x.
Proof.
 apply Nat.leb_gt.
Qed.

(** Substraction in Option.

    In natural numbers, Coq usual subtrsaction is truncated:
    when a < b, one has a - b = 0.
    Here, one uses [None] to indicate this and [Some] to
    indicate an "exact" subtraction. *)

Fixpoint safe_minus a b : option nat :=
 match b, a with
   | 0, _ => Some a
   | S b, 0 => None
   | S b, S a => safe_minus a b
 end.

Lemma safe_minus_spec a b :
 match safe_minus a b with
 | Some c => a = b + c
 | None => a < b
 end.
Proof.
 revert b; induction a; destruct b; simpl; auto with arith.
 specialize (IHa b). destruct (safe_minus a b); auto with arith.
Qed.

Lemma safe_minus_ge a b :
  b <= a -> safe_minus a b = Some (a - b).
Proof.
  revert b.
  induction a; destruct b; intro H; try reflexivity.
  - contradiction (Nat.nle_succ_0 b H).
  - rewrite Nat.sub_succ.
      apply IHa.
      apply le_S_n.
      apply H.
Qed.

Lemma safe_minus_lt a b :
  a < b -> safe_minus a b = None.
Proof.
  revert a.
  induction b; intro a.
  - intro H.
    contradiction (Nat.nle_succ_0 a H).
  - destruct a; intro H.
    + reflexivity.
    + apply IHb.
      apply le_S_n.
      apply H.
Qed.

Lemma safe_minus_le_a a b n :
  safe_minus a b = Some n -> n <= a.
Proof.
  revert b.
  induction a; destruct b; intro H; try (injection H; intro H1; rewrite <- H1; apply Nat.le_refl).
  - discriminate H.
  - apply le_S.
    apply IHa with (b := b).
    apply H.
Qed.

(** Accessing the n-th element in a list

   NB: list_get exists also in the standard library,
   as List.nth_error. *)

Fixpoint list_get {A} (l:list A) i : option A :=
  match i,l with
    | 0,   x::_ => Some x
    | S j, _::l => list_get l j
    | _, _ => None
  end.

Definition option_map {A B} (f:A->B) (o:option A) :=
  match o with
    | Some a => Some (f a)
    | None => None
  end.

Fixpoint list_set {A} (l:list A) i x : option (list A) :=
  match i,l with
    | 0, _::l => Some (x::l)
    | S j, a::l => option_map (cons a) (list_set l j x)
    | _, _ => None
  end.

Lemma get_app_l {A} (l l':list A) (n:nat) : n < length l ->
  list_get (l++l') n = list_get l n.
Proof.
 revert l.
 induction n; destruct l; simpl; auto with arith; inversion 1.
Qed.

Lemma get_app_r {A} (l l':list A) (n:nat) :
  list_get (l++l') (length l + n) = list_get l' n.
Proof.
 induction l; auto.
Qed.

Lemma get_app_r0 {A} (l l':list A) (n:nat) : n = length l ->
  list_get (l++l') n = list_get l' 0.
Proof.
  intros. rewrite <- (get_app_r l l'). f_equal. lia.
Qed.

Lemma get_app_r' {A} (l l':list A) (n:nat) : length l <= n ->
  list_get (l++l') n = list_get l' (n-length l).
Proof.
 intros. rewrite <- (get_app_r l l'). f_equal. lia.
Qed.

Lemma get_None {A} (l:list A) n :
 list_get l n = None <-> length l <= n.
Proof.
 revert n. induction l; destruct n; simpl; rewrite ?IHl; split;
  auto with arith; inversion 1.
Qed.

Lemma get_Some {A} (l:list A) n x :
 list_get l n = Some x -> n < length l.
Proof.
 revert n. induction l; destruct n; simpl; try discriminate.
  - auto with arith.
  - intros. apply IHl in H. auto with arith.
Qed.

Global Hint Resolve get_Some : core.
Open Scope string_scope.

(** Equivalent of List.assoc, specialized for [string]. 
Here [=?] is [String.eqb] *)

Fixpoint lookup {A} (s:string) (l:list (string*A)) (default:A) :=
  match l with
    | nil => default
    | (x,d)::l => if s =? x then d else lookup s l default
  end.

(** Index of an element in a list, specialized for `string` *)

Fixpoint index (s:string) (l:list string) :=
  match l with
    | nil => 0
    | x::l => if s =? x then 0 else S (index s l)
  end.

Open Scope list_scope.

(** Summation operator : sum f x n = f x + ... + f (x+n).
    Beware, there are  (n+1) terms in this sum...
    In particular sum f 0 n = f 0 + ... + f n. *)

Fixpoint sum f x k :=
  match k with
    | 0 => f x
    | S n' => f x + sum f (S x) n'
  end.

Compute sum (fun _ => 1) 0 10. (* 11 *)
Compute sum (fun x => x) 0 10. (* 0 + 1 + ... + 10 = 55 *)

(** II) Arithmetical expressions with summations *)

(** Expressions *)

Definition var := string.

Inductive op := Plus | Minus | Mult.

Inductive expr :=
  | EInt : nat -> expr
  | EVar : var -> expr
  | EOp  : op -> expr -> expr -> expr
  | ESum : var -> expr -> expr -> expr.

(** (ESum var max body) is the sum of the values of [body]
    when var takes  values from  0 to max
    (included). For example, here is the sum of squares from 0 to 10,
    written sum(x^2,x=0..10) in Maple or
    $\sum_{x=0}^{10}{x^2}$ in LaTeX. *)

Definition test1 :=
  ESum "x" (EInt 10) (EOp Mult (EVar "x") (EVar "x")).

(** More complex, a double summation:
    sum(sum(x*y,y=0..x),x=0..10) *)

Definition test2 :=
  ESum "x" (EInt 10)
   (ESum "y" (EVar "x")
     (EOp Mult (EVar "x") (EVar "y"))).


(** Evaluating expressions *)

Definition eval_op o :=
  match o with
    | Plus => plus
    | Minus => minus
    | Mult => mult
  end.

Fixpoint eval (env:list (string*nat)) e :=
  match e with
    | EInt n => n
    | EVar v => lookup v env 0
    | EOp o e1 e2 => eval_op o (eval env e1) (eval env e2)
    | ESum v efin ecorps => sum (fun x => eval ((v,x)::env) ecorps) 0 (eval env efin)
  end.

Compute (eval nil test1). (* 385 expected: n(n+1)(2n+1)/6 for n=10 *)
Compute (eval nil test2). (* 1705 expected result *)


(** III) Stack machine *)

(** Our machine is made of two stacks : a main stack to store 
computations and an auxiliary stack of  variables. Instructions
are stored eleswhere. *)

Record machine :=
  Mach {
      (** Code Pointer *)
      pc : nat;
      (** Main stack *)
      stack : list nat;
      (** Variables stack *)
      vars : list nat
    }.

Definition initial_machine := Mach 0 nil nil.

Inductive instr :=
  (** Push a integer value to the stack. *)
  | Push : nat -> instr
  (** Pop the value from the top of the stack. *)
  | Pop : instr
  (** Pop two values and push the result of the binary operation. *)
  | Op : op -> instr
  (** Creates a new variable on top of the variables stack,
      initialized to 0. *)
  | NewVar : instr
  (** Remove a variable from the top of the variables stack.
      Its current value is lost. *)
  | DelVar : instr
  (** Push a value equal to the  i-th variable on the stack. *)
  | GetVar : nat -> instr
  (** Pop the value on the top of the stack and store it to the 
  i-th variable. *)
  | SetVar : nat -> instr
  (** Jump offset: remove  offset from the code pointer if the
  first variable is less than or equal to the top of the stack.
     Stack and variables are left unchanged. *)
  | Jump : nat -> instr.

(* NB: There is no Halt instruction, one stops when 
   pc goes beyond the end of the code. *)

(* Reference Semantics for instructions,
   defined via an inductive relation *)

Inductive Stepi : instr -> machine -> machine -> Prop :=
| SPush pc stk vs n :
    Stepi (Push n) (Mach pc stk vs) (Mach (S pc) (n::stk) vs)
| SPop pc stk vs x :
    Stepi Pop (Mach pc (x::stk) vs) (Mach (S pc) stk vs)
| SOp pc stk vs o y x :
    Stepi (Op o) (Mach pc (y::x::stk) vs)
                 (Mach (S pc) (eval_op o x y :: stk) vs)
| SNewVar pc stk vs :
    Stepi NewVar (Mach pc stk vs) (Mach (S pc) stk (0::vs))
| SDelVar pc stk vs x :
    Stepi DelVar (Mach pc stk (x::vs)) (Mach (S pc) stk vs)
| SGetVar pc stk vs i x :
    list_get vs i = Some x ->
    Stepi (GetVar i) (Mach pc stk vs) (Mach (S pc) (x::stk) vs)
| SSetVar pc stk vs vs' i x :
    list_set vs i x = Some vs' ->
    Stepi (SetVar i) (Mach pc (x::stk) vs)
                     (Mach (S pc) stk vs')
| SJumpYes pc stk vs v x off : off <= pc -> v <= x ->
    Stepi (Jump off) (Mach pc (x::stk) (v::vs))
                     (Mach (pc-off) (x::stk) (v::vs))
| SJumpNo pc stk vs v x off : x < v ->
    Stepi (Jump off) (Mach pc (x::stk) (v::vs))
                     (Mach (S pc) (x::stk) (v::vs)).

Definition Step (code:list instr) (m m' : machine) : Prop :=
 match list_get code m.(pc) with
  | Some instr => Stepi instr m m'
  | None => False
 end.

Inductive Steps (code:list instr) : machine -> machine -> Prop :=
 | NoStep m : Steps code m m
 | SomeSteps m1 m2 m3 :
     Step code m1 m2 -> Steps code m2 m3 -> Steps code m1 m3.

(** state : state of a machine, that is its computation stack 
together with its variables stack, but not its code pointer. *)

Definition state := (list nat * list nat)%type.

(** A complete execution goes from  pc=0 to pc=(length code) *)

Definition Exec code '(stk, vs) '(stk', vs') :=
  Steps code (Mach 0 stk vs) (Mach (length code) stk' vs').

(** Run : relation between the code and the result of 
its execution. *)

Definition Run code res := Exec code (nil,nil) (res::nil,nil).

(** Small example using this semantics *)

Lemma Run_example :
  Run (Push 7 :: Push 3 :: Op Minus :: nil) 4.
Proof.
  repeat econstructor.
Qed.

(** Basic properties of Steps : transitivity, ... *)

Global Hint Constructors Stepi Steps : core.

Lemma Steps_trans code m1 m2 m3 :
 Steps code m1 m2 -> Steps code m2 m3 -> Steps code m1 m3.
Proof.
  induction 1; intro H1; eauto.
Qed.

Lemma OneStep code st st' : Step code st st' -> Steps code st st'.
Proof.
  eauto.
Qed.

(** Shifting the pc in a machine *)

Definition shift_pc k (p:machine) :=
  let '(Mach pc stk vars) := p in
  (Mach (k+pc) stk vars).

Lemma pc_shift n m : (shift_pc n m).(pc) = n + m.(pc).
Proof.
  now destruct m.
Qed.

(** Adding code before / after the zone of interest *)

Lemma Step_extend code code' m m' :
  Step code m m' -> Step (code++code') m m'.
Proof.
  unfold Step.
  edestruct le_gt_dec.
  - now rewrite (proj2 (get_None code (pc m)) l).
  - erewrite get_app_l; auto.
Qed.

Lemma Steps_extend code code' m m' :
 Steps code m m' -> Steps (code++code') m m'.
Proof.
  induction 1.
  - apply NoStep.
  - apply SomeSteps with (m2 := m2).
    + apply Step_extend.
      assumption.
    + assumption.
Qed.

Lemma Stepi_shift instr n m m' :
 Stepi instr m m' ->
 Stepi instr (shift_pc n m) (shift_pc n m').
Proof.
  destruct 1; unfold shift_pc; try rewrite Nat.add_succ_r with (n := n) (m := pc0); eauto.
  rewrite Nat.add_sub_assoc with (n := n) (m := pc0) (p := off).
    - apply SJumpYes.
      + eapply Nat.le_trans; eauto with arith.
      + assumption.
    - assumption.
Qed.

Lemma Step_shift code0 code m m' (n := List.length code0) :
 Step code m m' ->
 Step (code0 ++ code) (shift_pc n m) (shift_pc n m').
Proof.
  unfold Step.
  rewrite pc_shift with (m := m) (n := n).
  unfold n.
  rewrite get_app_r with (l := code0) (l' := code) (n := pc m).
  case (list_get code (pc m)).
  - intro instr.
    apply Stepi_shift.
  - intro H.
    assumption.
Qed.

Lemma Steps_shift code0 code  m m' (n := List.length code0) :
 Steps code m m' ->
 Steps (code0 ++ code) (shift_pc n m) (shift_pc n m').
Proof.
  induction 1.
  - apply NoStep.
  - apply SomeSteps with (m2 := shift_pc n m2).
    + apply Step_shift.
      assumption.
    + assumption.
Qed.

(** Composition of complete executions *)

Lemma Exec_trans code1 code2 stk1 vars1 stk2 vars2 stk3 vars3 :
 Exec code1 (stk1, vars1) (stk2, vars2) ->
 Exec code2 (stk2, vars2) (stk3, vars3) ->
 Exec (code1 ++ code2) (stk1, vars1) (stk3, vars3).
Proof.
  simpl.
  intros H1 H2.
  apply Steps_trans with (m2 := Mach (length code1) stk2 vars2).
  - apply Steps_extend.
    assumption.
  - rewrite <- Nat.add_0_r with (n := length code1).
    rewrite app_length.
    apply Steps_shift with (m := Mach 0 stk2 vars2) (m' := Mach (length code2) stk3 vars3).
    assumption.
Qed.


(** Correctness of jumps in a loop:

    - Variable 0 is the variable for loop a,
    - Variable 1 is the accumulator acc
    - The top of the stack is the upper limit b
    of the loop variable

    One first shows that if a code adds f(a) to acc and
    increments a, then repeting this  (via a later Jump)
    will add (sum f a (b-a)) to acc.
    Variable N (of vaue b-a) is the number of loop round
    to make.
*)

(** The following lemma is hard. You can first skip it and come back later, after finishing part IV... *)

Global Hint Resolve le_n_S le_plus_r : core.

Lemma Steps_jump code n (f:nat->nat) stk vars b :
  length code = n ->
  (forall a acc,
   Steps code
         (Mach 0 (b::stk) (a::acc::vars))
         (Mach n (b::stk) ((S a)::(acc + f a)::vars)))
  ->
  forall N a acc,
    b = N + a ->
    Steps (code++(Jump n)::nil)
          (Mach 0 (b::stk) (a::acc::vars))
          (Mach (S n) (b::stk) ((S b)::(acc + sum f a N)::vars)).
Proof.
  intros Hlength Hloop N.
  apply eq_sym in Hlength.
  induction N; intros a acc Heqb; simpl sum.
  - apply Steps_trans with (m2 := Mach n (b::stk) (S a::acc + f a::vars)).
    + apply Steps_extend.
      apply Hloop.
    + apply SomeSteps with (m2 := Mach (S n) (b::stk) (S b::acc + f a::vars)).
      * unfold Step.
        simpl pc.
        rewrite get_app_r0.
          simpl.
          rewrite Nat.add_0_l in Heqb.
          rewrite Heqb.
          apply SJumpNo.
          apply Nat.le_refl.
          apply Hlength.
      * apply NoStep.
  - rewrite Nat.add_succ_l in Heqb.
    rewrite <- Nat.add_succ_r in Heqb.
    rewrite Nat.add_assoc.
    apply Steps_trans with (m2 := Mach 0 (b::stk) (S a::acc + f a::vars)).
    + apply Steps_trans with (m2 := Mach n (b::stk) (S a::acc + f a::vars)).
      * apply Steps_extend.
        apply Hloop.
      * apply SomeSteps with (m2 := Mach 0 (b::stk) (S a::acc + f a::vars)).
          unfold Step.
          simpl pc.
          rewrite get_app_r0.
            simpl.
            rewrite <- Nat.sub_diag with (n := n).
            apply SJumpYes.
              apply Nat.le_refl.
              rewrite Heqb.
              apply Nat.le_add_l.
            apply Hlength.
          apply NoStep.
    + apply IHN.
      apply Heqb.
Qed.

(** Specialized version of the previous result, with
    Exec instead of Step, and 0 as initial value for loop variables
    and accumulators. *)

Lemma Exec_jump code (f:nat->nat) stk vars b :
  (forall a acc,
     Exec code (b::stk, a::acc::vars)
               (b::stk, (S a)::(acc + f a)::vars))
  ->
  Exec (code++(Jump (length code))::nil)
      (b::stk, 0::0::vars)
      (b::stk, (S b)::(sum f 0 b)::vars).
Proof.
  intro H.
  unfold Exec.
  rewrite app_length.
  simpl.
  rewrite Nat.add_1_r.
  apply Steps_jump with (code := code) (n := length code) (f := f) (stk := stk) (vars := vars) (b := b) (a := 0) (acc := 0).
  - reflexivity.
  - apply H.
  - symmetry.
    apply Nat.add_0_r.
Qed.

(** IV) The compiler

    One transforms an expression into a series of instructions
    for the stack machine.

    Conventions:
     - At any loop entry, one created two variables,
       the loop variable and the accumulator.
     - Loop variables always have even positions in the variable 
     stack.
     - the compilation environment cenv contains only
       loop variables.
    See also the invariant EnvsOk below for details. *)

Fixpoint comp (cenv:list string) e :=
  match e with
    | EInt n => Push n :: nil
    | EVar v => GetVar (index v cenv * 2) :: nil
    | EOp o e1 e2 => comp cenv e1 ++ comp cenv e2 ++ Op o :: nil
    | ESum v e1 e2 =>
      let prologue := (comp cenv e1) ++ NewVar :: NewVar :: nil in
      let corps := (comp (v::cenv) e2) ++ GetVar 1 :: Op Plus :: SetVar 1 :: GetVar 0 :: Push 1 :: Op Plus :: SetVar 0 :: nil in
      let boucle := corps ++ Jump (length corps) :: nil in
      let epilogue := Pop :: GetVar 1 :: DelVar :: DelVar :: nil in
      prologue ++ boucle ++ epilogue
  end.

Definition compile e := comp nil e.

(** Free variables in an expression *)

Inductive FV (v:var) : expr -> Prop :=
| FVVar : FV v (EVar v)
| FVOpl op e1 e2 : FV v e1 -> FV v (EOp op e1 e2)
| FVOpr op e1 e2 : FV v e2 -> FV v (EOp op e1 e2)
| FVSumfin v' e1 e2 : FV v e1 -> FV v (ESum v' e1 e2)
| FVSumcorps v' e1 e2 : (v =? v') = false -> FV v e2 -> FV v (ESum v' e1 e2).

Global Hint Constructors FV : core.

Definition Closed e := forall v, ~ FV v e.

(** Environment invariants.
    env : evaluation environment (list (string*nat))
    cenv : compilation environment (list string)
    vars : stack variable for the machines *)

Definition EnvsOk e env cenv vars :=
 forall v, FV v e ->
   In v cenv /\
   list_get vars (index v cenv * 2) = Some (lookup v env 0).

Global Hint Unfold EnvsOk : core.

Lemma EnvsOk_ESum v e1 e2 env cenv vars a b :
  EnvsOk (ESum v e1 e2) env cenv vars ->
  EnvsOk e2 ((v,a)::env) (v::cenv) (a::b::vars).
Proof.
  unfold EnvsOk.
  intros H v' HFV.
  split; destruct (Bool.bool_dec (v' =? v) true).
  - apply String.eqb_eq in e.
    rewrite e.
    apply in_eq.
  - apply in_cons.
    apply H.
    apply FVSumcorps.
    apply Bool.not_true_iff_false.
    apply n.
    apply HFV.
  - simpl.
    rewrite e.
    reflexivity.
  - simpl.
    apply Bool.not_true_iff_false in n.
    rewrite n.
    simpl.
    apply H.
    apply FVSumcorps.
    + apply n.
    + apply HFV.
Qed.

(** Compiler correctness *)

Ltac basic_exec :=
  (* This tactics proves goal (Exec code m m')
      when the code and the machine m are known in detail. *)
  unfold Exec; repeat (eapply SomeSteps; [constructor|]);
   try apply NoStep; try reflexivity.

(* Note that if you think you are proving something impossible,
if may be a sign that you got the wrong definition for comp. *)

Theorem comp_ok e env cenv vars stk :
 EnvsOk e env cenv vars ->
 Exec (comp cenv e) (stk,vars) (eval env e :: stk, vars).
Proof.
  revert stk vars env cenv.
  induction e; intros stk vars env cenv H.
  - basic_exec.
  - basic_exec.
    apply H.
    apply FVVar.
  - simpl.
    apply Exec_trans with (stk2 := eval env e1 :: stk) (vars2 := vars).
    + apply IHe1.
      unfold EnvsOk.
      intros v Hv.
      apply H.
      apply FVOpl.
      apply Hv.
    + apply Exec_trans with (stk2 := eval env e2 :: eval env e1 :: stk) (vars2 := vars).
      * apply IHe2.
        unfold EnvsOk.
        intros v Hv.
        apply H.
        apply FVOpr.
        apply Hv.
      * basic_exec.
  - simpl eval.
    simpl comp.
    apply Exec_trans with (code1 := comp cenv e1 ++ NewVar :: NewVar :: nil) (stk2 := eval env e1 :: stk) (vars2 := 0 :: 0 :: vars).
    + apply Exec_trans with (stk2 := eval env e1 :: stk) (vars2 := vars).
      apply IHe1.
      * unfold EnvsOk.
        intros v0 Hv0.
        apply H.
        apply FVSumfin.
        apply Hv0.
      * basic_exec.
    + apply Exec_trans with (stk2 := eval env e1 :: stk) (vars2 := S (eval env e1) :: sum (fun x => eval ((v, x) :: env) e2) 0 (eval env e1) :: vars).
      * apply Exec_jump.
        intros a acc.
        apply Exec_trans with (stk2 := eval ((v,a)::env) e2 :: eval env e1 :: stk) (vars2 := a :: acc :: vars).
          apply IHe2.
          apply EnvsOk_ESum with (e1 := e1).
          apply H.
          basic_exec.
          simpl.
          rewrite Nat.add_1_r.
          rewrite Nat.add_comm.
          reflexivity.
      * basic_exec.
Qed.

Theorem compile_ok e : Closed e -> Run (compile e) (eval nil e).
Proof.
  intro H.
  apply comp_ok.
  intros v H1.
  contradiction (H v H1).
Qed.

(** V) Executable semantics

    Instead of the previous relations (Step*, Exec, Run...),
    one know wants to get a function computing the result of
    executing a stack machine. *)

(** This part is much harder that the previous one and
it is optional. *)

Open Scope nat_scope.

Inductive step_result : Type :=
  | More : machine -> step_result (* calcul en cours *)
  | Stop : machine -> step_result (* calcul fini (pc hors code) *)
  | Bug : step_result. (* situation illégale, machine plantée *)

(** For function [step] below, these two monadic operators
    may help (even thoug this is essentially a matter of 
    taste...). *)

Definition option_bind {A} (o:option A) (f : A -> step_result) :=
  match o with
    | None => Bug
    | Some x => f x
  end.

Infix ">>=" := option_bind (at level 20, left associativity).

Definition list_bind {A} (l:list A) (f:A->list A->step_result) :=
 match l with
  | nil => Bug
  | x::l => f x l
 end.

Infix "::>" := list_bind (at level 20, left associativity).

(** One step of computation *)

Definition step code (m:machine) : step_result :=
  let '(Mach pc stk vars) := m in
  (** usual answer: *)
  let more := fun stk vars => More (Mach (S pc) stk vars) in
  match list_get code pc with
    | None => Stop m
    | Some instr => match instr with
      | Push n => more (n::stk) vars
      | Pop => stk ::> (fun x stk => more stk vars)
      | Op o => stk ::> (fun y stk => stk ::> (fun x stk => more (eval_op o x y :: stk) vars))
      | NewVar => more stk (0 :: vars)
      | DelVar => vars ::> (fun v vars => more stk vars)
      | GetVar i => list_get vars i >>= (fun v => more (v :: stk) vars)
      | SetVar i => stk ::> (fun x stk => option_bind (list_set vars i x) (fun vars => more stk vars))
      | Jump off => stk ::> (fun x _ => vars ::> (fun v _ =>
                      if v <=? x then
                        safe_minus pc off >>= (fun pc => More (Mach pc stk vars))
                      else
                       more stk vars
                      ))
      end
    end.

(** The [steps] function iterates [step] [count] many times
    (or less if [Stop _] or [Bug] are reached before...). *)

Fixpoint steps count (code : list instr) (m : machine) :=
  match count with
    | 0 => More m
    | S count' => match step code m with
                    | More m' => steps count' code m'
                    | Stop m' => Stop m'
                    | Bug => Bug
                  end
  end.

(** Function [run] executes a certain code from the initial
    machine, then extracts the result.
    One returns  [None] if the computation is not finished
    after [count] steps, or if there is a problem during 
    execution or in the end state (eg. empty final stack,
    non empty final variables, etc). *)

Definition run (count : nat) (code : list instr) : option nat :=
  match steps count code (Mach 0 nil nil) with
    | Stop m => match m with
                  | Mach _ (x :: nil) nil => Some x
                  | _ => None
                end
    | _ => None
  end.

Compute (run 1000 (compile test1)). (* expected value: Some 385 *)
Compute (run 1000 (compile test2)). (* expected value: Some 1705 *)

(** Equivalence between the two semantics *)

(** TODO: in this part, you have to step yourself the intermediate results. *)

Lemma step_equiv code (m1 m2 : machine) :
  Step code m1 m2 <-> step code m1 = More m2.
Proof.
  unfold Step.
  remember (list_get code (pc m1)) as i.
  destruct i.
  - split.
    + destruct 1; simpl pc in Heqi; unfold step; rewrite <- Heqi;
      try simpl list_bind; try simpl option_bind; try rewrite H; try reflexivity.
      * rewrite (proj2 (Nat.leb_le v x) H0).
        rewrite (safe_minus_ge pc0 off H).
        reflexivity.
      * rewrite (proj2 (Nat.leb_gt v x) H).
        reflexivity.
    + destruct m1.
      simpl pc in Heqi.
      unfold step.
      rewrite <- Heqi.
      destruct i.
      * injection 1.
        intro H1.
        rewrite <- H1.
        apply SPush.
      * destruct stack0; simpl list_bind.
          discriminate 1.
          injection 1.
          intro H1.
          rewrite <- H1.
          apply SPop.
      * destruct stack0; simpl list_bind.
          discriminate 1.
          destruct stack0; simpl list_bind.
            discriminate 1.
            injection 1.
            intro H1.
            rewrite <- H1.
            apply SOp.
      * injection 1.
        intro H1.
        rewrite <- H1.
        apply SNewVar.
      * destruct vars0; simpl list_bind.
          discriminate 1.
          injection 1.
          intro H1.
          rewrite <- H1.
          apply SDelVar.
      * remember (list_get vars0 n) as vi.
        destruct vi; simpl option_bind.
          injection 1.
          intro H1.
          rewrite <- H1.
          apply SGetVar.
          symmetry.
          apply Heqvi.
          discriminate 1.
      * destruct stack0; simpl list_bind.
          discriminate 1.
          remember (list_set vars0 n n0) as vars1.
          destruct vars1; simpl option_bind.
            injection 1.
            intro H1.
            rewrite <- H1.
            apply SSetVar.
            symmetry.
            apply Heqvars1.
            discriminate 1.
      * destruct stack0; simpl list_bind.
          discriminate 1.
          destruct vars0; simpl list_bind.
            discriminate 1.
              destruct (Nat.le_gt_cases n1 n0).
                rewrite (proj2 (Nat.leb_le n1 n0) H).
                destruct (Nat.le_gt_cases n pc0).
                  rewrite (safe_minus_ge pc0 n H0).
                  simpl option_bind.
                  injection 1.
                  intro H2.
                  rewrite <- H2.
                  apply SJumpYes.
                    apply H0.
                    apply H.
                  rewrite (safe_minus_lt pc0 n H0).
                  simpl option_bind.
                  discriminate 1.
                rewrite (proj2 (Nat.leb_gt n1 n0) H).
                  injection 1.
                  intro H1.
                  rewrite <- H1.
                  apply SJumpNo.
                  apply H.
  - split.
    + intro H. contradiction H.
    + destruct m1.
      simpl pc in Heqi.
      unfold step.
      rewrite <- Heqi.
      discriminate 1.
Qed.

Lemma steps_equiv code m1 m2 :
  Steps code m1 m2 <-> exists count, steps count code m1 = More m2.
Proof.
  split; intro H.
  - induction H.
    + exists 0.
      reflexivity.
    + destruct IHSteps.
      exists (S x).
      simpl steps.
      rewrite (proj1 (step_equiv code m1 m2) H).
      apply H1.
  - destruct H.
    revert m1 H.
    induction x; intro m1.
    + injection 1.
      intro H1.
      rewrite <- H1.
      apply NoStep.
    + simpl steps.
      remember (step code m1) as m.
      destruct m; try discriminate 1.
      intro H.
      apply SomeSteps with (m2 := m).
        * apply step_equiv.
          symmetry.
          apply Heqm.
        * apply IHx.
          apply H.
Qed.

Lemma steps_trans count1 count2 code m1 m2 :
  steps count1 code m1 = More m2 -> steps (count1+count2) code m1 = steps count2 code m2.
Proof.
  revert m1.
  induction count1; intro m1.
  - simpl.
    injection 1.
    intro H1.
    rewrite <- H1.
    reflexivity.
  - simpl.
    remember (step code m1) as m.
    destruct m; try discriminate 1.
    apply IHcount1.
Qed.

Lemma step_pc_S code m1 m2 :
  step code m1 = More m2 -> pc m2 <= S (pc m1).
Proof.
  destruct m1.
  unfold step.
  destruct (list_get code pc0).
  - destruct i.
    + injection 1.
      intro H1.
      rewrite <- H1.
      apply Nat.le_refl.
    + destruct stack0; simpl list_bind.
      * discriminate 1.
      * injection 1.
        intro H1.
        rewrite <- H1.
        apply Nat.le_refl.
    + destruct stack0; simpl list_bind.
      * discriminate 1.
      * destruct stack0; simpl list_bind.
          discriminate 1.
          injection 1.
          intro H1.
          rewrite <- H1.
          apply Nat.le_refl.
    + injection 1.
      intro H1.
      rewrite <- H1.
      apply Nat.le_refl.
    + destruct vars0; simpl list_bind.
      * discriminate 1.
      * injection 1.
        intro H1.
        rewrite <- H1.
        apply Nat.le_refl.
    + destruct (list_get vars0 n); simpl option_bind.
      * injection 1.
        intro H1.
        rewrite <- H1.
        apply Nat.le_refl.
      * discriminate 1.
    + destruct stack0; simpl list_bind.
      * discriminate 1.
      * destruct (list_set vars0 n n0); simpl option_bind.
          injection 1.
          intro H1.
          rewrite <- H1.
          apply Nat.le_refl.
          discriminate 1.
    + destruct stack0; simpl list_bind.
      * discriminate 1.
      * destruct vars0; simpl list_bind.
          discriminate 1.
          destruct (n1 <=? n0).
            remember (safe_minus pc0 n) as pc1.
            destruct pc1; simpl option_bind.
              injection 1.
              intro H1.
              rewrite <- H1.
              apply le_S.
              apply safe_minus_le_a with (b := n).
              symmetry.
              apply Heqpc1.
              discriminate 1.
            injection 1.
            intro H1.
            rewrite <- H1.
            apply Nat.le_refl.
  - discriminate 1.
Qed.

Lemma stop_equiv code m1 m2 :
  step code m1 = Stop m2 -> m1 = m2 /\ pc m1 >= length code.
Proof.
  destruct m1.
  unfold step.
  remember (list_get code pc0) as i.
  destruct i.
  - destruct i; try discriminate 1.
    + destruct stack0; discriminate 1.
    + destruct stack0; simpl list_bind.
      * discriminate 1.
      * destruct stack0; discriminate 1.
    + destruct vars0; discriminate 1.
    + destruct (list_get vars0 n); discriminate 1.
    + destruct stack0; simpl list_bind.
      * discriminate 1.
      * destruct (list_set vars0 n n0); discriminate 1.
    + destruct stack0; simpl list_bind.
      * discriminate 1.
      * destruct vars0; simpl list_bind.
          discriminate 1.
          destruct (n1 <=? n0).
            destruct (safe_minus pc0 n); discriminate 1.
            discriminate 1.
  - injection 1.
    intro H1.
    split.
    + apply H1.
    + apply get_None.
      symmetry.
      apply Heqi.
Qed.

Lemma last_step code m pc0 stk0 vars0 :
  pc m <= length code -> (exists count, steps count code m = Stop (Mach pc0 stk0 vars0)) -> exists count', steps count' code m = More (Mach (length code) stk0 vars0).
Proof.
  intros H H0.
  destruct H0.
  revert m H H0.
  induction x.
  - discriminate 2.
  - intros m H.
    simpl steps.
    destruct (le_lt_eq_dec (pc m) (length code) H).
    + simpl steps.
      remember (step code m) as m0.
      destruct m0.
      * intro H1.
        destruct IHx with (m := m0).
          apply Nat.le_trans with (m := S (pc m)).
            apply step_pc_S with (code := code).
            symmetry.
            apply Heqm0.
            apply l.
          apply H1.
        exists (S x0).
        simpl steps.
        rewrite <- Heqm0.
        apply H0.
      * contradiction (Nat.nle_succ_diag_l (pc m) (Nat.le_trans (S (pc m)) (length code) (pc m) l (proj2 (stop_equiv code m m0 (eq_sym Heqm0))))).
      * discriminate 1.
    + destruct m.
      unfold step.
      rewrite (proj2 (get_None code pc1)).
      * injection 1.
        intros H1 H2 H3.
        exists 0.
        rewrite <- e.
        rewrite H1.
        rewrite H2.
        reflexivity.
      * rewrite <- e.
        reflexivity.
Qed.

Lemma run_equiv code res :
 Run code res <-> exists count, run count code = Some res.
Proof.
  split; intro H.
  - destruct (proj1 (steps_equiv code (Mach 0 nil nil) (Mach (length code) (res :: nil) nil)) H).
    exists (x + 1).
    unfold run.
    rewrite steps_trans with (m2 := Mach (length code) (res :: nil) nil).
    simpl.
    rewrite (proj2 (get_None code (length code)) (Nat.le_refl (length code))).
    reflexivity.
    apply H0.
  - apply steps_equiv.
    destruct H.
    unfold run in H.
    remember (steps x code (Mach 0 nil nil)) as m.
    destruct m; try discriminate H.
    destruct m.
    destruct stack0; try destruct stack0; destruct vars0; try discriminate H.
    injection H.
    intro H1.
    apply last_step with (pc0 := pc0).
    + apply Nat.le_0_l.
    + exists x.
      symmetry.
      rewrite <- H1.
      apply Heqm.
Qed.

(** Here is the  main theorem formulated for run *)

Theorem run_compile e :
 Closed e ->
 exists count, run count (compile e) = Some (eval nil e).
Proof.
  intro H.
  apply run_equiv.
  apply compile_ok.
  apply H.
Qed.
