(** * Semantics.v — Small-Step Operational Semantics

    Defines:
    - Runtime configuration (expression, world state, audit trace)
    - Handler abstraction (axiomatized)
    - 9 core reduction rules
    - Multi-step reduction

    Corresponds to semantics.tex §4
    RunbookFX ICFP 2026 — Mechanized Metatheory *)

Require Import Arith.
Require Import Lia.
Require Import List.
Require Import EffectAlgebra.
Require Import Syntax.
Require Import Typing.

(* ================================================================= *)
(** ** 1. Runtime State (Axiomatized)                                 *)
(* ================================================================= *)

(** World state: the infrastructure state (Kubernetes clusters,
    telemetry stores, etc.). We axiomatize this as an abstract type. *)
Parameter sigma : Type.

(** Audit trace entry. *)
Parameter trace_entry : Type.

(** Audit trace: list of entries. *)
Definition trace := list trace_entry.

(** Rollback token representation at runtime. *)
Parameter token_val : Type.

(* ================================================================= *)
(** ** 2. Handler Abstraction (Axiomatized)                           *)
(* ================================================================= *)

(** A handler H provides implementations for observe, act, and rollback.
    We axiomatize these as parameters, following the paper's parametric
    treatment (Definition 3, semantics.tex). *)

(** Handler observation: H_c^obs(v, σ) → (result, σ)
    Observation preserves world state. *)
Parameter handler_obs : CapName -> expr -> sigma -> expr * sigma.

(** Handler action: H_c^act(v, σ) → ((result, token), σ')
    Action modifies world state and produces a rollback token. *)
Parameter handler_act : CapName -> expr -> sigma ->
  expr * expr * sigma.

(** Handler rollback: H^undo(token, σ) → σ'
    Rollback restores the relevant component of world state. *)
Parameter handler_undo : expr -> sigma -> sigma.

(** Handler observation preserves σ. *)
Axiom handler_obs_preserves_state : forall c v s r s',
  handler_obs c v s = (r, s') -> s = s'.

(** Handler action result is a value. *)
Axiom handler_act_result_value : forall c v s r tok s',
  handler_act c v s = (r, tok, s') -> is_value r /\ is_value tok.

(** Handler observation result is a value. *)
Axiom handler_obs_result_value : forall c v s r s',
  handler_obs c v s = (r, s') -> is_value r.

(** Handler observation produces a closed value of type TResult c.
    Closed values are typable in any context with the bottom effect. *)
Axiom handler_obs_result_typing : forall Gu Ga kappa c v s r s',
  handler_obs c v s = (r, s') ->
  has_type Gu Ga kappa r (TResult c) eff_bot.

(** Handler action produces a closed value of type TActResult c and
    a closed rollback token, both typable in any context with eff_bot. *)
Axiom handler_act_result_typing : forall Gu Ga kappa c v s r tok s',
  handler_act c v s = (r, tok, s') ->
  has_type Gu Ga kappa r (TActResult c) eff_bot /\
  has_type Gu Ga kappa tok TRollback eff_bot.

(** Well-formed handler: defined for all capabilities in κ. *)
Definition handler_well_formed (kappa : CapSet) : Prop :=
  forall c, cap_mem c kappa ->
    (forall v s, exists r s', handler_obs c v s = (r, s')) /\
    (forall v s, exists r tok s', handler_act c v s = (r, tok, s')).

(* ================================================================= *)
(** ** 3. Small-Step Reduction                                        *)
(* ================================================================= *)

(** Trace append helper. *)
Parameter mk_obs_entry  : CapName -> expr -> expr -> trace_entry.
Parameter mk_act_entry  : CapName -> expr -> expr -> expr -> trace_entry.
Parameter mk_undo_entry : expr -> trace_entry.

(** Small-step reduction: ⟨e, σ, θ⟩ → ⟨e', σ', θ'⟩

    We define 9 core rules:
    E-Beta, E-Let, E-LetPair, E-Observe, E-Act, E-Rollback,
    E-GuardTrue, E-GuardFalse, E-Context *)

Inductive step :
  expr -> sigma -> trace ->
  expr -> sigma -> trace -> Prop :=

  (* -------- E-Beta --------
     (λx:τ.e) v → e[v/x] *)
  | E_Beta : forall T body v s th,
      is_value v ->
      step (EApp (EAbs T body) v) s th
           (subst_top v body) s th

  (* -------- E-Let --------
     let x = v in e → e[v/x] *)
  | E_Let : forall v e2 s th,
      is_value v ->
      step (ELet v e2) s th
           (subst_top v e2) s th

  (* -------- E-LetPair --------
     let (x,t) = (v₁, v₂) in e → e[v₁/x, v₂/t] *)
  | E_LetPair : forall v1 v2 e2 s th,
      is_value v1 -> is_value v2 ->
      step (ELetPair (EPair v1 v2) e2) s th
           (subst_pair v1 v2 e2) s th

  (* -------- E-Observe --------
     observe_c v → H_c^obs(v, σ)
     σ unchanged, trace extended *)
  | E_Observe : forall c v s th r s',
      is_value v ->
      handler_obs c v s = (r, s') ->
      step (EObserve c v) s th
           r s' (th ++ (mk_obs_entry c v r :: nil))

  (* -------- E-Act --------
     act_c v → (result, token)
     σ modified, trace extended *)
  | E_Act : forall c v s th r tok s',
      is_value v ->
      handler_act c v s = (r, tok, s') ->
      step (EAct c v) s th
           (EPair r tok) s' (th ++ (mk_act_entry c v r tok :: nil))

  (* -------- E-Rollback --------
     rollback token → ()
     σ restored, trace extended *)
  | E_Rollback : forall tok s th s',
      is_value tok ->
      handler_undo tok s = s' ->
      step (ERollback tok) s th
           EUnit s' (th ++ (mk_undo_entry tok :: nil))

  (* -------- E-GuardTrue --------
     guard true e → Some e *)
  | E_GuardTrue : forall e s th,
      step (EGuard ETrue e) s th
           (ESome e) s th

  (* -------- E-GuardFalse --------
     guard false e → None *)
  | E_GuardFalse : forall e T s th,
      step (EGuard EFalse e) s th
           (ENone T) s th

  (* -------- Congruence rules --------
     Reduce in evaluation position *)

  (* App: reduce function position *)
  | E_App1 : forall e1 e1' e2 s th s' th',
      step e1 s th e1' s' th' ->
      step (EApp e1 e2) s th (EApp e1' e2) s' th'

  (* App: reduce argument position (function is a value) *)
  | E_App2 : forall v1 e2 e2' s th s' th',
      is_value v1 ->
      step e2 s th e2' s' th' ->
      step (EApp v1 e2) s th (EApp v1 e2') s' th'

  (* Let: reduce binding *)
  | E_Let1 : forall e1 e1' e2 s th s' th',
      step e1 s th e1' s' th' ->
      step (ELet e1 e2) s th (ELet e1' e2) s' th'

  (* LetPair: reduce pair expression *)
  | E_LetPair1 : forall e1 e1' e2 s th s' th',
      step e1 s th e1' s' th' ->
      step (ELetPair e1 e2) s th (ELetPair e1' e2) s' th'

  (* Observe: reduce argument *)
  | E_Observe1 : forall c e e' s th s' th',
      step e s th e' s' th' ->
      step (EObserve c e) s th (EObserve c e') s' th'

  (* Act: reduce argument *)
  | E_Act1 : forall c e e' s th s' th',
      step e s th e' s' th' ->
      step (EAct c e) s th (EAct c e') s' th'

  (* Rollback: reduce argument *)
  | E_Rollback1 : forall e e' s th s' th',
      step e s th e' s' th' ->
      step (ERollback e) s th (ERollback e') s' th'

  (* Guard: reduce condition *)
  | E_Guard1 : forall ec ec' eb s th s' th',
      step ec s th ec' s' th' ->
      step (EGuard ec eb) s th (EGuard ec' eb) s' th'

  (* Pair: reduce left *)
  | E_Pair1 : forall e1 e1' e2 s th s' th',
      step e1 s th e1' s' th' ->
      step (EPair e1 e2) s th (EPair e1' e2) s' th'

  (* Pair: reduce right (left is value) *)
  | E_Pair2 : forall v1 e2 e2' s th s' th',
      is_value v1 ->
      step e2 s th e2' s' th' ->
      step (EPair v1 e2) s th (EPair v1 e2') s' th'

  (* Some: reduce argument *)
  | E_Some1 : forall e e' s th s' th',
      step e s th e' s' th' ->
      step (ESome e) s th (ESome e') s' th'.

Hint Constructors step : core.

(** Multi-step reduction (reflexive transitive closure). *)
Inductive multi_step :
  expr -> sigma -> trace ->
  expr -> sigma -> trace -> Prop :=
  | MS_Refl : forall e s th,
      multi_step e s th e s th
  | MS_Step : forall e1 s1 th1 e2 s2 th2 e3 s3 th3,
      step e1 s1 th1 e2 s2 th2 ->
      multi_step e2 s2 th2 e3 s3 th3 ->
      multi_step e1 s1 th1 e3 s3 th3.

Hint Constructors multi_step : core.

(** End of Semantics.v *)
