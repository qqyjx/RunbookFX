(** * Syntax.v — Core Calculus Syntax and Substitution

    Defines the simplified RunbookFX core calculus:
    - Types (base, pairs, functions, Option, RollbackToken)
    - Expressions (λ-calculus + observe/act/rollback/guard)
    - Values
    - De Bruijn substitution

    Corresponds to Figure 2 (dsl.tex) — simplified core.
    RunbookFX ICFP 2026 — Mechanized Metatheory *)

Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import List.
Require Import EffectAlgebra.

(* ================================================================= *)
(** ** 1. Types                                                       *)
(* ================================================================= *)

(** Simplified type system for the core calculus.
    We omit: LogStream, MetricSeries, TraceGraph, Evidence, Hypothesis,
    Topology, List, effect polymorphism types. *)
Inductive ty : Type :=
  | TUnit     : ty
  | TBool     : ty
  | TBase     : nat -> ty            (* indexed base types *)
  | TPair     : ty -> ty -> ty       (* τ₁ × τ₂ *)
  | TArrow    : ty -> ty -> ty       (* τ₁ → τ₂ *)
  | TOption   : ty -> ty             (* Option τ *)
  | TRollback : ty                   (* RollbackToken (affine) *)
  | TQuery    : CapName -> ty        (* Query_c *)
  | TResult   : CapName -> ty        (* Result_c *)
  | TAction   : CapName -> ty        (* Action_c *)
  | TActResult : CapName -> ty.      (* τ_c (result of act_c) *)

(** Type equality decidability. *)
(* We axiomatize this to avoid a large mutual recursion. *)
Axiom ty_eq_dec : forall (t1 t2 : ty), {t1 = t2} + {t1 <> t2}.

(* ================================================================= *)
(** ** 2. Expressions                                                 *)
(* ================================================================= *)

(** Core calculus expressions using de Bruijn indices.
    We include the 12 core constructs from the mechanization plan:
    - Variables, lambda, application, let, let-pair
    - observe, act, rollback, guard
    - Unit and Bool literals, pair construction *)
Inductive expr : Type :=
  (* Core lambda calculus *)
  | EVar      : nat -> expr                      (* de Bruijn variable *)
  | EAbs      : ty -> expr -> expr               (* λ x:τ. e *)
  | EApp      : expr -> expr -> expr             (* e₁ e₂ *)
  (* Binding *)
  | ELet      : expr -> expr -> expr             (* let x = e₁ in e₂ *)
  | ELetPair  : expr -> expr -> expr             (* let (x,t) = e₁ in e₂ *)
  (* Effect operations *)
  | EObserve  : CapName -> expr -> expr          (* observe_c e *)
  | EAct      : CapName -> expr -> expr          (* act_c e *)
  | ERollback : expr -> expr                     (* rollback e *)
  (* Control flow *)
  | EGuard    : expr -> expr -> expr             (* guard e_cond e_body *)
  (* Literals *)
  | EUnit     : expr                             (* () *)
  | ETrue     : expr                             (* true *)
  | EFalse    : expr                             (* false *)
  | EPair     : expr -> expr -> expr             (* (e₁, e₂) *)
  | ESome     : expr -> expr                     (* Some e *)
  | ENone     : ty -> expr.                      (* None : Option τ *)

(* ================================================================= *)
(** ** 3. Values                                                      *)
(* ================================================================= *)

(** Value predicate: identifies expressions that are fully reduced. *)
Inductive is_value : expr -> Prop :=
  | V_Unit   : is_value EUnit
  | V_True   : is_value ETrue
  | V_False  : is_value EFalse
  | V_Abs    : forall T e, is_value (EAbs T e)
  | V_Pair   : forall v1 v2, is_value v1 -> is_value v2 ->
                is_value (EPair v1 v2)
  | V_Some   : forall v, is_value v -> is_value (ESome v)
  | V_None   : forall T, is_value (ENone T).

Hint Constructors is_value : core.

(** Boolean decidability of being a value. *)
Fixpoint is_value_b (e : expr) : bool :=
  match e with
  | EUnit       => true
  | ETrue       => true
  | EFalse      => true
  | EAbs _ _    => true
  | EPair e1 e2 => is_value_b e1 && is_value_b e2
  | ESome e     => is_value_b e
  | ENone _     => true
  | _           => false
  end.

(* ================================================================= *)
(** ** 4. De Bruijn Shifting and Substitution                         *)
(* ================================================================= *)

(** Shift: increase free variables ≥ cutoff by d. *)
Fixpoint shift (d : nat) (c : nat) (e : expr) : expr :=
  match e with
  | EVar n       => if le_lt_dec c n then EVar (n + d) else EVar n
  | EAbs T body  => EAbs T (shift d (S c) body)
  | EApp e1 e2   => EApp (shift d c e1) (shift d c e2)
  | ELet e1 e2   => ELet (shift d c e1) (shift d (S c) e2)
  | ELetPair e1 e2 => ELetPair (shift d c e1) (shift d (S (S c)) e2)
  | EObserve cap e => EObserve cap (shift d c e)
  | EAct cap e   => EAct cap (shift d c e)
  | ERollback e  => ERollback (shift d c e)
  | EGuard e1 e2 => EGuard (shift d c e1) (shift d c e2)
  | EUnit        => EUnit
  | ETrue        => ETrue
  | EFalse       => EFalse
  | EPair e1 e2  => EPair (shift d c e1) (shift d c e2)
  | ESome e      => ESome (shift d c e)
  | ENone T      => ENone T
  end.

(** Substitution: [j := s] e — replace variable j with s in e. *)
Fixpoint subst (j : nat) (s : expr) (e : expr) : expr :=
  match e with
  | EVar n       => if Nat.eq_dec n j then s
                     else if le_lt_dec j n then EVar (pred n)
                     else EVar n
  | EAbs T body  => EAbs T (subst (S j) (shift 1 0 s) body)
  | EApp e1 e2   => EApp (subst j s e1) (subst j s e2)
  | ELet e1 e2   => ELet (subst j s e1) (subst (S j) (shift 1 0 s) e2)
  | ELetPair e1 e2 =>
      ELetPair (subst j s e1) (subst (S (S j)) (shift 2 0 s) e2)
  | EObserve cap e => EObserve cap (subst j s e)
  | EAct cap e   => EAct cap (subst j s e)
  | ERollback e  => ERollback (subst j s e)
  | EGuard e1 e2 => EGuard (subst j s e1) (subst j s e2)
  | EUnit        => EUnit
  | ETrue        => ETrue
  | EFalse       => EFalse
  | EPair e1 e2  => EPair (subst j s e1) (subst j s e2)
  | ESome e      => ESome (subst j s e)
  | ENone T      => ENone T
  end.

Notation "'[' j ':=' s ']' e" := (subst j s e) (at level 20).

(** Top-level substitution for beta-reduction: [0 := v] e *)
Definition subst_top (v e : expr) : expr :=
  subst 0 v e.

(** Simultaneous substitution for let-pair: substitute two values at
    indices 0 and 1. We substitute the second (index 1) first,
    then the first (index 0). *)
Definition subst_pair (v1 v2 e : expr) : expr :=
  subst 0 v1 (subst 0 (shift 1 0 v2) e).

(** End of Syntax.v *)
