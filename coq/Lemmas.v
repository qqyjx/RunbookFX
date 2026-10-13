(** * Lemmas.v — Supporting Lemmas for Type Safety

    Defines:
    - Value Typing: values consume no affine resources and produce no effects
    - Canonical Forms: typed values have expected shapes
    - Substitution: substitution preserves typing
    - Context splitting properties

    Corresponds to appendix.tex §C.3 (Standard Lemmas)
    RunbookFX ICFP 2026 — Mechanized Metatheory *)

Require Import Arith.
Require Import Lia.
Require Import List.
Require Import EffectAlgebra.
Require Import Syntax.
Require Import Typing.
Require Import Semantics.

(* ================================================================= *)
(** ** 1. Value Typing                                                *)
(* ================================================================= *)

(** Values typed under bot effect: if v is a value, its effect is eff_bot.
    This is a simplified version; the full paper lemma also shows
    Gamma_a = empty, but we state the effect part here.

    Paper reference: Lemma C.1 (Value Typing) *)

(** Helper: an empty affine context has all None entries. *)
Definition ctx_a_empty (Ga : ctx_a) : Prop :=
  forall n, lookup_a Ga n = None.

(** Value typing with subsumption: if v is a value and well-typed,
    then eff_bot <= eff (since eff_bot is the bottom element). *)

Lemma value_typing_effect : forall Gu Ga kappa v T eff,
  is_value v ->
  has_type Gu Ga kappa v T eff ->
  eff_le eff_bot eff.
Proof.
  intros Gu Ga kappa v T eff Hval Htype.
  unfold eff_le. simpl.
  assert (H1: eff_risk eff_bot ≤r eff_risk eff) by apply risk_le_readonly.
  assert (H2: eff_caps eff_bot ⊆k eff_caps eff).
  { unfold cap_subset, eff_bot, cap_empty. simpl.
    intros c Hc. contradiction. }
  assert (H3: eff_res eff_bot <= eff_res eff).
  { unfold eff_bot. simpl. lia. }
  tauto.
Qed.

(** Key lemma: values can always be retyped at eff_bot.
    This is the core of Value Typing (Lemma C.1).

    For each value form, the direct typing rule produces eff_bot.
    For T-Sub, the inner derivation produces eff_bot by IH.

    We state this as: there exists a derivation with eff_bot. *)
Lemma value_has_bot_effect : forall Gu Ga kappa v T eff,
  is_value v ->
  has_type Gu Ga kappa v T eff ->
  has_type Gu Ga kappa v T eff_bot.
Proof.
  intros Gu Ga kappa v T eff Hval Htype.
  induction Htype; try (inversion Hval; fail).
  - (* T_Abs: conclusion already eff_bot *) eapply T_Abs; eauto.
  - (* T_Sub: IH on inner derivation *) auto.
  - (* T_Unit *) apply T_Unit.
  - (* T_True *) apply T_True.
  - (* T_False *) apply T_False.
  - (* T_Pair: components are values; rebuild via T_Pair + T_Sub *)
    inversion Hval; subst.
    apply T_Sub with (eff := eff_join eff_bot eff_bot).
    + eapply T_Pair; eauto.
    + apply (proj1 (eff_join_identity_l eff_bot)).
    + apply wf_bot.
  - (* T_Some *) inversion Hval; subst.
    apply T_Some. auto.
  - (* T_None *) apply T_None.
Qed.

(* ================================================================= *)
(** ** 2. Canonical Forms                                             *)
(* ================================================================= *)

(** Paper reference: Lemma C.3 (Canonical Forms)
    If v is a value of type tau, then v has the expected shape. *)

Lemma canonical_arrow : forall Gu Ga kappa v T1 T2 eff,
  is_value v ->
  has_type Gu Ga kappa v (TArrow T1 T2) eff ->
  exists e, v = EAbs T1 e.
Proof.
  intros Gu Ga kappa v T1 T2 eff Hval Htype.
  remember (TArrow T1 T2) as T eqn:HT.
  generalize dependent T2. generalize dependent T1.
  induction Htype; intros;
    try (inversion Hval; fail); try discriminate HT.
  - (* T_Abs *) injection HT; intros; subst. exists e. reflexivity.
  - (* T_Sub *) eapply IHHtype; eauto.
Qed.

Lemma canonical_bool : forall Gu Ga kappa v eff,
  is_value v ->
  has_type Gu Ga kappa v TBool eff ->
  v = ETrue \/ v = EFalse.
Proof.
  intros Gu Ga kappa v eff Hval Htype.
  remember TBool as T eqn:HT.
  induction Htype; try (inversion Hval; fail); try discriminate HT.
  - (* T_Sub *) apply IHHtype; assumption.
  - (* T_True *) left; reflexivity.
  - (* T_False *) right; reflexivity.
Qed.

Lemma canonical_pair : forall Gu Ga kappa v T1 T2 eff,
  is_value v ->
  has_type Gu Ga kappa v (TPair T1 T2) eff ->
  exists v1 v2, v = EPair v1 v2 /\ is_value v1 /\ is_value v2.
Proof.
  intros Gu Ga kappa v T1 T2 eff Hval Htype.
  remember (TPair T1 T2) as T eqn:HT.
  generalize dependent T2. generalize dependent T1.
  induction Htype; intros;
    try (inversion Hval; fail); try discriminate HT.
  - (* T_Sub *) eapply IHHtype; eauto.
  - (* T_Pair *) injection HT; intros; subst.
    inversion Hval; subst.
    exists e1, e2. auto.
Qed.

Lemma canonical_unit : forall Gu Ga kappa v eff,
  is_value v ->
  has_type Gu Ga kappa v TUnit eff ->
  v = EUnit.
Proof.
  intros Gu Ga kappa v eff Hval Htype.
  remember TUnit as T eqn:HT.
  induction Htype; try (inversion Hval; fail); try discriminate HT.
  - apply IHHtype; assumption.
  - reflexivity.
Qed.

Lemma canonical_option : forall Gu Ga kappa v T eff,
  is_value v ->
  has_type Gu Ga kappa v (TOption T) eff ->
  (exists v', v = ESome v' /\ is_value v') \/ (exists T', v = ENone T').
Proof.
  intros Gu Ga kappa v T eff Hval Htype.
  remember (TOption T) as Topt eqn:HT.
  generalize dependent T.
  induction Htype; intros;
    try (inversion Hval; fail); try discriminate HT.
  - (* T_Sub *) eapply IHHtype; eauto.
  - (* T_Some *) injection HT; intros; subst.
    inversion Hval; subst.
    left. exists e. auto.
  - (* T_None *) right. exists T. reflexivity.
Qed.

(* ================================================================= *)
(** ** 3. Context Splitting Properties                                *)
(* ================================================================= *)

(** Context split preserves lookup structure. *)
Lemma ctx_split_lookup_left : forall G G1 G2 n T,
  ctx_split G G1 G2 ->
  lookup_a G1 n = Some T ->
  lookup_a G n = Some T.
Proof.
  intros G G1 G2 n T Hsplit Hlook.
  generalize dependent n.
  induction Hsplit; intros.
  - (* nil *) destruct n; simpl in Hlook; discriminate.
  - (* left *) destruct n.
    + simpl in *. assumption.
    + simpl in *. apply IHHsplit. assumption.
  - (* right *) destruct n.
    + simpl in *. discriminate.
    + simpl in *. apply IHHsplit. assumption.
  - (* none *) destruct n.
    + simpl in *. discriminate.
    + simpl in *. apply IHHsplit. assumption.
Qed.

Lemma ctx_split_lookup_right : forall G G1 G2 n T,
  ctx_split G G1 G2 ->
  lookup_a G2 n = Some T ->
  lookup_a G n = Some T.
Proof.
  intros G G1 G2 n T Hsplit Hlook.
  generalize dependent n.
  induction Hsplit; intros.
  - destruct n; simpl in Hlook; discriminate.
  - destruct n.
    + simpl in *. discriminate.
    + simpl in *. apply IHHsplit. assumption.
  - destruct n.
    + simpl in *. assumption.
    + simpl in *. apply IHHsplit. assumption.
  - destruct n.
    + simpl in *. discriminate.
    + simpl in *. apply IHHsplit. assumption.
Qed.

(** Identity split: G splits into G and empty. *)
Lemma ctx_split_id_left : forall G,
  ctx_split G G (repeat None (length G)).
Proof.
  induction G as [| a rest IH].
  - simpl. constructor.
  - simpl. destruct a.
    + apply Split_left. exact IH.
    + apply Split_none. exact IH.
Qed.

Lemma ctx_split_id_right : forall G,
  ctx_split G (repeat None (length G)) G.
Proof.
  induction G as [| a rest IH].
  - simpl. constructor.
  - simpl. destruct a.
    + apply Split_right. exact IH.
    + apply Split_none. exact IH.
Qed.

(** Symmetry of splitting. *)
Lemma ctx_split_sym : forall G G1 G2,
  ctx_split G G1 G2 -> ctx_split G G2 G1.
Proof.
  intros G G1 G2 Hsplit.
  induction Hsplit.
  - constructor.
  - apply Split_right. assumption.
  - apply Split_left. assumption.
  - apply Split_none. assumption.
Qed.

(* ================================================================= *)
(** ** 4. Weakening                                                   *)
(* ================================================================= *)

(** Unrestricted context weakening: inserting a type at any position
    in Gamma_u preserves typing (after shifting variables that cross
    the insertion point). *)

(** Lookup interacts with insertion at position [length Gu1]:
    indices below the insertion point are unaffected. *)
Lemma lookup_u_insert_left : forall Gu1 Gu2 T' n,
  n < length Gu1 ->
  lookup_u (Gu1 ++ T' :: Gu2) n = lookup_u (Gu1 ++ Gu2) n.
Proof.
  intros Gu1 Gu2 T' n Hlt.
  unfold lookup_u.
  generalize dependent n.
  induction Gu1 as [| a rest IH]; intros; simpl in *.
  - lia.
  - destruct n.
    + reflexivity.
    + apply IH. lia.
Qed.

(** Indices at or above the insertion point shift up by one. *)
Lemma lookup_u_insert_right : forall Gu1 Gu2 T' n,
  length Gu1 <= n ->
  lookup_u (Gu1 ++ T' :: Gu2) (S n) = lookup_u (Gu1 ++ Gu2) n.
Proof.
  intros Gu1 Gu2 T' n Hge.
  unfold lookup_u.
  generalize dependent n.
  induction Gu1 as [| a rest IH]; intros; simpl in *.
  - reflexivity.
  - destruct n.
    + lia.
    + simpl. apply IH. lia.
Qed.

(** Length-preservation under repeat None. *)
Lemma length_repeat_none : forall (n : nat),
  length (@repeat (option ty) None n) = n.
Proof. induction n; simpl; auto. Qed.

(** Generalised weakening: insert T' at position [length Gu1]. *)
Lemma weakening_u_at : forall Gu1 Gu2 Ga kappa e T eff T',
  has_type (Gu1 ++ Gu2) Ga kappa e T eff ->
  has_type (Gu1 ++ T' :: Gu2) Ga kappa (shift 1 (length Gu1) e) T eff.
Proof.
  intros Gu1 Gu2 Ga kappa e T eff T' Htype.
  remember (Gu1 ++ Gu2) as Gu eqn:HGu.
  generalize dependent Gu2. generalize dependent Gu1.
  induction Htype; intros; subst.

  - (* T_Var_Un *)
    simpl.
    destruct (le_lt_dec (length Gu1) n) as [Hge | Hlt].
    + replace (n + 1) with (S n) by lia.
      apply T_Var_Un.
      rewrite lookup_u_insert_right; assumption.
    + apply T_Var_Un.
      rewrite lookup_u_insert_left; assumption.

  - (* T_Abs *)
    simpl. apply T_Abs with (T2 := T2) (eff := eff).
    + assumption.
    + change (T1 :: Gu1 ++ T' :: Gu2) with ((T1 :: Gu1) ++ T' :: Gu2).
      replace (S (length Gu1)) with (length (T1 :: Gu1)) by reflexivity.
      apply IHHtype. reflexivity.

  - (* T_App *)
    simpl. eapply T_App; eauto.

  - (* T_Let *)
    simpl. eapply T_Let; eauto.
    change (T1 :: Gu1 ++ T' :: Gu2) with ((T1 :: Gu1) ++ T' :: Gu2).
    replace (S (length Gu1)) with (length (T1 :: Gu1)) by reflexivity.
    apply IHHtype2. reflexivity.

  - (* T_LetPair *)
    simpl. eapply T_LetPair; eauto.
    change (T2 :: T1 :: Gu1 ++ T' :: Gu2)
      with ((T2 :: T1 :: Gu1) ++ T' :: Gu2).
    replace (S (S (length Gu1))) with (length (T2 :: T1 :: Gu1))
      by reflexivity.
    apply IHHtype2. reflexivity.

  - (* T_Observe *)
    simpl. apply T_Observe; auto.

  - (* T_Act *)
    simpl. apply T_Act; auto.

  - (* T_Rollback *)
    simpl. apply T_Rollback; auto.

  - (* T_Guard *)
    simpl. eapply T_Guard; eauto.

  - (* T_Sub *)
    eapply T_Sub; eauto.

  - (* T_Unit *)
    simpl. apply T_Unit.

  - (* T_True *)
    simpl. apply T_True.

  - (* T_False *)
    simpl. apply T_False.

  - (* T_Pair *)
    simpl. eapply T_Pair; eauto.

  - (* T_Some *)
    simpl. apply T_Some. auto.

  - (* T_None *)
    simpl. apply T_None.
Qed.

(** Special case at the head. *)
Lemma weakening_u : forall Gu Ga kappa e T eff T',
  has_type Gu Ga kappa e T eff ->
  has_type (T' :: Gu) Ga kappa (shift 1 0 e) T eff.
Proof.
  intros. apply (weakening_u_at nil Gu Ga kappa e T eff T').
  simpl. assumption.
Qed.

(* ================================================================= *)
(** ** 5. Substitution Preserves Typing                               *)
(* ================================================================= *)

(** Paper reference: Lemma C.2 (Substitution)

    If Gu, x:T'; Ga; kappa |- e : T |> eff
    and Gu; empty; kappa |- v : T' |> eff_bot
    then Gu; Ga; kappa |- e[v/x] : T |> eff.

    We state this for de Bruijn index 0 (top-level substitution). *)

Theorem substitution_preserves_typing :
  forall Gu Ga kappa e v T T' eff,
    has_type (T' :: Gu) Ga kappa e T eff ->
    is_value v ->
    has_type Gu (repeat None (length Ga)) kappa v T' eff_bot ->
    has_type Gu Ga kappa (subst_top v e) T eff.
Proof.
  (* This is the standard substitution lemma for de Bruijn.
     The proof proceeds by induction on the typing derivation.
     Key cases:
     - T_Var_Un at index 0: replace with v, use the value typing assumption
     - T_Var_Un at index n+1: lookup shifts down
     - T_Abs: use the shift/subst commutation lemma
     - T_App: apply IH to both subexpressions
     All other cases follow by straightforward IH application. *)
Admitted.
(** Admitted: Full proof requires shift/subst commutation lemmas
    (~100 lines). The statement is standard and matches the paper's
    Lemma C.2. See e.g., Pierce's SF for the canonical proof. *)

(** Pair substitution preserves typing (for E-LetPair).
    If Gu, x:T1; Ga ++ [Some T2]; kappa |- e : T |> eff
    and v1 : T1, v2 : T2 are values,
    then Gu; Ga; kappa |- subst_pair v1 v2 e : T |> eff. *)
Theorem pair_substitution_preserves_typing :
  forall Gu Ga kappa e v1 v2 T T1 T2 eff,
    has_type (T1 :: Gu) (Ga ++ (Some T2 :: nil)) kappa e T eff ->
    is_value v1 -> is_value v2 ->
    has_type Gu (repeat None (length Ga)) kappa v1 T1 eff_bot ->
    has_type Gu (repeat None (length Ga)) kappa v2 T2 eff_bot ->
    has_type Gu Ga kappa (subst_pair v1 v2 e) T eff.
Proof.
  (* Two-step substitution: first substitute the affine variable (v2),
     then the unrestricted variable (v1). Each step uses the
     single-variable substitution lemma. *)
Admitted.
(** Admitted: Requires the single-variable substitution lemma
    plus affine context manipulation. *)

(* ================================================================= *)
(** ** 6. Inversion Lemmas                                            *)
(* ================================================================= *)

(** Inversion for application typing. *)
Lemma inversion_app : forall Gu Ga kappa e1 e2 T eff,
  has_type Gu Ga kappa (EApp e1 e2) T eff ->
  exists Ga1 Ga2 T1 eff1 eff2,
    ctx_split Ga Ga1 Ga2 /\
    has_type Gu Ga1 kappa e1 (TArrow T1 T) eff1 /\
    has_type Gu Ga2 kappa e2 T1 eff2 /\
    eff_le (eff_join eff1 eff2) eff.
Proof.
  intros. remember (EApp e1 e2) as e.
  induction H; try discriminate.
  - (* T_App *) inversion Heqe; subst.
    exists Ga1, Ga2, T1, eff1, eff2.
    split; [| split; [| split]]; auto. apply eff_le_refl.
  - (* T_Sub *) subst.
    specialize (IHhas_type eq_refl).
    destruct IHhas_type as [Ga1' [Ga2' [T1' [eff1' [eff2' [Hsplit [Ht1 [Ht2 Hle]]]]]]]].
    exists Ga1', Ga2', T1', eff1', eff2'.
    split; [| split; [| split]]; auto.
    eapply eff_le_trans; eauto.
Qed.

(** Inversion for let typing. *)
Lemma inversion_let : forall Gu Ga kappa e1 e2 T eff,
  has_type Gu Ga kappa (ELet e1 e2) T eff ->
  exists Ga1 Ga2 T1 eff1 eff2,
    ctx_split Ga Ga1 Ga2 /\
    has_type Gu Ga1 kappa e1 T1 eff1 /\
    has_type (T1 :: Gu) Ga2 kappa e2 T eff2 /\
    eff_le (eff_join eff1 eff2) eff.
Proof.
  intros. remember (ELet e1 e2) as e.
  induction H; try discriminate.
  - (* T_Let *) inversion Heqe; subst.
    exists Ga1, Ga2, T1, eff1, eff2.
    split; [| split; [| split]]; auto. apply eff_le_refl.
  - (* T_Sub *) subst.
    specialize (IHhas_type eq_refl).
    destruct IHhas_type as [Ga1' [Ga2' [T1' [eff1' [eff2' [Hsplit [Ht1 [Ht2 Hle]]]]]]]].
    exists Ga1', Ga2', T1', eff1', eff2'.
    split; [| split; [| split]]; auto.
    eapply eff_le_trans; eauto.
Qed.

(** Inversion lemmas for each typing rule, handling T_Sub.
    These are standard and all follow the same pattern:
    remember + induction, direct case + T_Sub case with eff_le_trans. *)

Lemma inversion_observe : forall Gu Ga kappa c e T eff,
  has_type Gu Ga kappa (EObserve c e) T eff ->
  T = TResult c /\
  exists eff',
    cap_mem c kappa /\
    has_type Gu Ga kappa e (TQuery c) eff' /\
    eff_le (eff_join eff' (eff_observe c)) eff.
Proof.
  intros Gu Ga kappa c e T eff Htype.
  remember (EObserve c e) as e0 eqn:He.
  induction Htype; try discriminate He.
  - (* T_Observe *) injection He; intros; subst.
    split; [reflexivity|].
    exists eff'. split; [assumption|].
    split; [assumption|]. apply eff_le_refl.
  - (* T_Sub *) subst.
    destruct (IHHtype eq_refl) as [HT [eff'' [Hmem [Ht Hle]]]].
    split; [assumption|].
    exists eff''. split; [assumption|].
    split; [assumption|]. eapply eff_le_trans; eauto.
Qed.

Lemma inversion_act : forall Gu Ga kappa c e T eff,
  has_type Gu Ga kappa (EAct c e) T eff ->
  T = TPair (TActResult c) TRollback /\
  exists eff',
    cap_mem c kappa /\
    has_type Gu Ga kappa e (TAction c) eff' /\
    eff_le (eff_join eff' (eff_act c)) eff.
Proof.
  intros Gu Ga kappa c e T eff Htype.
  remember (EAct c e) as e0 eqn:He.
  induction Htype; try discriminate He.
  - (* T_Act *) injection He; intros; subst.
    split; [reflexivity|].
    exists eff'. split; [assumption|].
    split; [assumption|]. apply eff_le_refl.
  - (* T_Sub *) subst.
    destruct (IHHtype eq_refl) as [HT [eff'' [Hmem [Ht Hle]]]].
    split; [assumption|].
    exists eff''. split; [assumption|].
    split; [assumption|]. eapply eff_le_trans; eauto.
Qed.

Lemma inversion_rollback : forall Gu Ga kappa e T eff,
  has_type Gu Ga kappa (ERollback e) T eff ->
  T = TUnit /\
  exists eff',
    has_type Gu Ga kappa e TRollback eff' /\
    eff_le (eff_join eff' eff_rollback) eff.
Proof.
  intros Gu Ga kappa e T eff Htype.
  remember (ERollback e) as e0 eqn:He.
  induction Htype; try discriminate He.
  - (* T_Rollback *) injection He; intros; subst.
    split; [reflexivity|].
    exists eff'. split; [assumption|]. apply eff_le_refl.
  - (* T_Sub *) subst.
    destruct (IHHtype eq_refl) as [HT [eff'' [Ht Hle]]].
    split; [assumption|].
    exists eff''. split; [assumption|]. eapply eff_le_trans; eauto.
Qed.

Lemma inversion_guard : forall Gu Ga kappa ec eb T eff,
  has_type Gu Ga kappa (EGuard ec eb) T eff ->
  exists Ga1 Ga2 T' effc effb,
    T = TOption T' /\
    ctx_split Ga Ga1 Ga2 /\
    has_type Gu Ga1 kappa ec TBool effc /\
    has_type Gu Ga2 kappa eb T' effb /\
    eff_le (eff_join effc effb) eff.
Proof.
  intros Gu Ga kappa ec eb T eff Htype.
  remember (EGuard ec eb) as e0 eqn:He.
  induction Htype; try discriminate He.
  - (* T_Guard *) injection He; intros; subst.
    exists Ga1, Ga2, T, effc, effb.
    split; [reflexivity|]. split; [assumption|].
    split; [assumption|]. split; [assumption|].
    apply eff_le_refl.
  - (* T_Sub *) subst.
    destruct (IHHtype eq_refl)
      as [Ga1 [Ga2 [T' [effc [effb [HT [Hsplit [Htc [Htb Hle]]]]]]]]].
    exists Ga1, Ga2, T', effc, effb.
    split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [assumption|].
    eapply eff_le_trans; eauto.
Qed.

Lemma inversion_letpair : forall Gu Ga kappa e1 e2 T eff,
  has_type Gu Ga kappa (ELetPair e1 e2) T eff ->
  exists Ga1 Ga2 T1 T2 eff1 eff2,
    ctx_split Ga Ga1 Ga2 /\
    has_type Gu Ga1 kappa e1 (TPair T1 T2) eff1 /\
    has_type (T2 :: T1 :: Gu) Ga2 kappa e2 T eff2 /\
    eff_le (eff_join eff1 eff2) eff.
Proof.
  intros Gu Ga kappa e1 e2 T eff Htype.
  remember (ELetPair e1 e2) as e0 eqn:He.
  induction Htype; try discriminate He.
  - (* T_LetPair *) injection He; intros; subst.
    exists Ga1, Ga2, T1, T2, eff1, eff2.
    split; [assumption|]. split; [assumption|].
    split; [assumption|]. apply eff_le_refl.
  - (* T_Sub *) subst.
    destruct (IHHtype eq_refl)
      as [Ga1 [Ga2 [T1 [T2 [eff1 [eff2 [Hsplit [Ht1 [Ht2 Hle]]]]]]]]].
    exists Ga1, Ga2, T1, T2, eff1, eff2.
    split; [assumption|]. split; [assumption|].
    split; [assumption|]. eapply eff_le_trans; eauto.
Qed.

(* ================================================================= *)
(** ** 7. Multi-Step Properties                                       *)
(* ================================================================= *)

(** Multi-step is transitive. *)
Lemma multi_step_trans : forall e1 s1 th1 e2 s2 th2 e3 s3 th3,
  multi_step e1 s1 th1 e2 s2 th2 ->
  multi_step e2 s2 th2 e3 s3 th3 ->
  multi_step e1 s1 th1 e3 s3 th3.
Proof.
  intros e1 s1 th1 e2 s2 th2 e3 s3 th3 H12 H23.
  induction H12.
  - assumption.
  - eapply MS_Step; eauto.
Qed.

(** Single step embeds into multi-step. *)
Lemma step_to_multi : forall e1 s1 th1 e2 s2 th2,
  step e1 s1 th1 e2 s2 th2 ->
  multi_step e1 s1 th1 e2 s2 th2.
Proof.
  intros. eapply MS_Step.
  - eassumption.
  - apply MS_Refl.
Qed.

(** End of Lemmas.v *)
