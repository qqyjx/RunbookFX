(** * Progress.v — Progress Theorem

    Theorem 3 (type_system.tex):
    If  Gu; Ga; kappa |- e : T |> eff  and  e is not a value,
    and  H is well-formed w.r.t. kappa,
    then there exist e', sigma', theta' such that
    <e, sigma, theta> -> <e', sigma', theta'>.

    RunbookFX ICFP 2026 — Mechanized Metatheory *)

Require Import Arith.
Require Import Lia.
Require Import List.
Require Import EffectAlgebra.
Require Import Syntax.
Require Import Typing.
Require Import Semantics.
Require Import Lemmas.

(* ================================================================= *)
(** ** Theorem 3: Progress                                            *)
(* ================================================================= *)

(** Progress: well-typed closed expressions are either values or can step.

    We state this for closed expressions (empty unrestricted context
    is not required — we allow open terms since the reduction rules
    handle variables via substitution before they become active).

    The key insight: handler well-formedness ensures that
    observe, act, and rollback always produce results. *)

Theorem progress : forall Ga kappa e T eff s th,
  has_type nil Ga kappa e T eff ->
  handler_well_formed kappa ->
  is_value e \/
  exists e' s' th', step e s th e' s' th'.
Proof.
  intros Ga kappa e T eff s th Htype Hwf.
  (* We proceed by induction on the typing derivation. *)
  remember (@nil ty) as Gu.
  induction Htype; subst.

  (* T_Var_Un: variable — impossible in empty context *)
  - (* lookup_u nil n = Some T is impossible *)
    destruct n; simpl in H; discriminate.

  (* T_Abs: lambda — already a value *)
  - left. constructor.

  (* T_App: e1 e2 — either e1 steps, or e1 is value and e2 steps,
     or both are values and canonical forms gives beta *)
  - right.
    destruct IHHtype1 as [Hv1 | [e1' [s1' [th1' Hs1]]]]; auto.
    + (* e1 is value *)
      destruct IHHtype2 as [Hv2 | [e2' [s2' [th2' Hs2]]]]; auto.
      * (* both values: canonical forms -> e1 is lambda *)
        destruct (canonical_arrow _ _ _ _ _ _ _ Hv1 Htype1) as [body Heq].
        subst. exists (subst_top e2 body), s, th.
        apply E_Beta. assumption.
      * (* e2 steps *)
        exists (EApp e1 e2'), s2', th2'.
        apply E_App2; assumption.
    + (* e1 steps *)
      exists (EApp e1' e2), s1', th1'.
      apply E_App1. assumption.

  (* T_Let: let x = e1 in e2 *)
  - right.
    destruct IHHtype1 as [Hv1 | [e1' [s1' [th1' Hs1]]]]; auto.
    + (* e1 is value *)
      exists (subst_top e1 e2), s, th.
      apply E_Let. assumption.
    + (* e1 steps *)
      exists (ELet e1' e2), s1', th1'.
      apply E_Let1. assumption.

  (* T_LetPair: let (x,t) = e1 in e2 *)
  - right.
    destruct IHHtype1 as [Hv1 | [e1' [s1' [th1' Hs1]]]]; auto.
    + (* e1 is value: canonical forms -> pair *)
      destruct (canonical_pair _ _ _ _ _ _ _ Hv1 Htype1) as [v1 [v2 [Heq [Hv1' Hv2']]]].
      subst. exists (subst_pair v1 v2 e2), s, th.
      apply E_LetPair; assumption.
    + (* e1 steps *)
      exists (ELetPair e1' e2), s1', th1'.
      apply E_LetPair1. assumption.

  (* T_Observe: observe_c e *)
  - right.
    destruct IHHtype as [Hv | [e'' [s'' [th'' Hs]]]]; auto.
    + (* e is value: handler provides result *)
      assert (Hwfc: (forall v s0, exists r s', handler_obs c v s0 = (r, s')) /\
                    (forall v s0, exists r tok s', handler_act c v s0 = (r, tok, s'))).
      { apply Hwf. assumption. }
      destruct Hwfc as [Hobs _].
      destruct (Hobs e s) as [r [s' Heq]].
      exists r, s', (th ++ (mk_obs_entry c e r :: nil)).
      apply E_Observe; assumption.
    + (* e steps *)
      exists (EObserve c e''), s'', th''.
      apply E_Observe1. assumption.

  (* T_Act: act_c e *)
  - right.
    destruct IHHtype as [Hv | [e'' [s'' [th'' Hs]]]]; auto.
    + (* e is value: handler provides result *)
      assert (Hwfc: (forall v s0, exists r s', handler_obs c v s0 = (r, s')) /\
                    (forall v s0, exists r tok s', handler_act c v s0 = (r, tok, s'))).
      { apply Hwf. assumption. }
      destruct Hwfc as [_ Hact].
      destruct (Hact e s) as [r [tok [s' Heq]]].
      exists (EPair r tok), s', (th ++ (mk_act_entry c e r tok :: nil)).
      apply E_Act; assumption.
    + (* e steps *)
      exists (EAct c e''), s'', th''.
      apply E_Act1. assumption.

  (* T_Rollback: rollback e *)
  - right.
    destruct IHHtype as [Hv | [e'' [s'' [th'' Hs]]]]; auto.
    + (* e is value: handler_undo is total by axiom *)
      exists EUnit, (handler_undo e s), (th ++ (mk_undo_entry e :: nil)).
      apply E_Rollback; auto.
    + (* e steps *)
      exists (ERollback e''), s'', th''.
      apply E_Rollback1. assumption.

  (* T_Guard: guard ec eb *)
  - right.
    destruct IHHtype1 as [Hvc | [ec' [sc' [thc' Hsc]]]]; auto.
    + (* ec is value: canonical forms -> true or false *)
      destruct (canonical_bool _ _ _ _ _ Hvc Htype1) as [Htrue | Hfalse].
      * subst. exists (ESome eb), s, th. apply E_GuardTrue.
      * subst. exists (ENone T), s, th. apply E_GuardFalse.
    + (* ec steps *)
      exists (EGuard ec' eb), sc', thc'.
      apply E_Guard1. assumption.

  (* T_Sub: subsumption — use IH *)
  - destruct (IHHtype eq_refl Hwf) as [Hv | Hstep]; auto.

  (* T_Unit, T_True, T_False: literals — values *)
  - left. constructor.
  - left. constructor.
  - left. constructor.

  (* T_Pair: (e1, e2) *)
  - destruct IHHtype1 as [Hv1 | [e1' [s1' [th1' Hs1]]]]; try tauto.
    + destruct IHHtype2 as [Hv2 | [e2' [s2' [th2' Hs2]]]]; try tauto.
      * left. apply V_Pair; assumption.
      * right. exists (EPair e1 e2'), s2', th2'.
        apply E_Pair2; assumption.
    + right. exists (EPair e1' e2), s1', th1'.
      apply E_Pair1. assumption.

  (* T_Some: Some e *)
  - destruct IHHtype as [Hv | [e' [s' [th' Hs]]]]; try tauto.
    + left. apply V_Some. assumption.
    + right. exists (ESome e'), s', th'.
      apply E_Some1. assumption.

  (* T_None: None T — value *)
  - left. constructor.
Qed.

(** End of Progress.v *)
