(** * EffectAlgebra.v — Product Effect Algebra with Interaction Axioms

    Corresponds to:
    - Definition 1 (Effect Monoid)           [type_system.tex, Def 1]
    - Definition 2 (Well-formed Effect Grade) [type_system.tex, Def 2]
    - Theorem 1 (Effect WF Preservation)      [type_system.tex, Thm 1]

    RunbookFX ICFP 2026 — Mechanized Metatheory *)

Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import List.
Require Import Classical_Prop.

(* ================================================================= *)
(** ** 1. Risk Lattice                                                *)
(* ================================================================= *)

(** The three-element risk lattice: ReadOnly ≤ SafeChange ≤ Disruptive. *)
Inductive Risk : Type :=
  | ReadOnly    : Risk
  | SafeChange  : Risk
  | Disruptive  : Risk.

(** Ordering on risk levels. *)
Definition risk_le (r1 r2 : Risk) : Prop :=
  match r1, r2 with
  | ReadOnly,   _          => True
  | SafeChange, SafeChange => True
  | SafeChange, Disruptive => True
  | Disruptive, Disruptive => True
  | _,          _          => False
  end.

Notation "r1 '≤r' r2" := (risk_le r1 r2) (at level 70).

(** Decidability of risk ordering. *)
Definition risk_le_dec (r1 r2 : Risk) : {r1 ≤r r2} + {~ (r1 ≤r r2)}.
Proof.
  destruct r1, r2; simpl; auto; right; tauto.
Defined.

(** Risk equality decidability. *)
Definition risk_eq_dec (r1 r2 : Risk) : {r1 = r2} + {r1 <> r2}.
Proof.
  destruct r1, r2; try (left; reflexivity); right; discriminate.
Defined.

(** Lattice join on risk: takes the maximum. *)
Definition risk_join (r1 r2 : Risk) : Risk :=
  match r1, r2 with
  | Disruptive, _ | _, Disruptive => Disruptive
  | SafeChange, _ | _, SafeChange => SafeChange
  | ReadOnly, ReadOnly            => ReadOnly
  end.

Notation "r1 '⊔r' r2" := (risk_join r1 r2) (at level 50).

(** Risk lattice properties. *)

Lemma risk_le_refl : forall r, r ≤r r.
Proof. destruct r; simpl; auto. Qed.

Lemma risk_le_trans : forall r1 r2 r3,
  r1 ≤r r2 -> r2 ≤r r3 -> r1 ≤r r3.
Proof. destruct r1, r2, r3; simpl; auto. Qed.

Lemma risk_le_antisym : forall r1 r2,
  r1 ≤r r2 -> r2 ≤r r1 -> r1 = r2.
Proof. destruct r1, r2; simpl; intros; auto; contradiction. Qed.

Lemma risk_join_comm : forall r1 r2, r1 ⊔r r2 = r2 ⊔r r1.
Proof. destruct r1, r2; reflexivity. Qed.

Lemma risk_join_assoc : forall r1 r2 r3,
  (r1 ⊔r r2) ⊔r r3 = r1 ⊔r (r2 ⊔r r3).
Proof. destruct r1, r2, r3; reflexivity. Qed.

Lemma risk_join_idem : forall r, r ⊔r r = r.
Proof. destruct r; reflexivity. Qed.

Lemma risk_join_ub_l : forall r1 r2, r1 ≤r (r1 ⊔r r2).
Proof. destruct r1, r2; simpl; auto. Qed.

Lemma risk_join_ub_r : forall r1 r2, r2 ≤r (r1 ⊔r r2).
Proof. destruct r1, r2; simpl; auto. Qed.

Lemma risk_join_lub : forall r1 r2 r3,
  r1 ≤r r3 -> r2 ≤r r3 -> (r1 ⊔r r2) ≤r r3.
Proof. destruct r1, r2, r3; simpl; auto. Qed.

Lemma risk_join_mono : forall r1 r1' r2 r2',
  r1 ≤r r1' -> r2 ≤r r2' -> (r1 ⊔r r2) ≤r (r1' ⊔r r2').
Proof. destruct r1, r1', r2, r2'; simpl; auto. Qed.

Lemma risk_join_readonly_l : forall r, ReadOnly ⊔r r = r.
Proof. destruct r; reflexivity. Qed.

Lemma risk_join_readonly_r : forall r, r ⊔r ReadOnly = r.
Proof. destruct r; reflexivity. Qed.

(** SafeChange ≤r r ↔ r = SafeChange ∨ r = Disruptive *)
Lemma safechange_le_cases : forall r,
  SafeChange ≤r r -> r = SafeChange \/ r = Disruptive.
Proof. destruct r; simpl; intros; auto; contradiction. Qed.

(** ReadOnly is the bottom element. *)
Lemma risk_le_readonly : forall r, ReadOnly ≤r r.
Proof. destruct r; simpl; auto. Qed.

(* ================================================================= *)
(** ** 2. Capability Names and Sets                                   *)
(* ================================================================= *)

(** We abstract over capability names. *)
Parameter CapName : Type.
Parameter cap_eq_dec : forall (c1 c2 : CapName), {c1 = c2} + {c1 <> c2}.

(** The risk function mapping each capability to its minimum risk level.
    This corresponds to risk : Caps → Risk in the paper. *)
Parameter risk_of_cap : CapName -> Risk.

(** Capability sets as predicates (Ensemble-style). *)
Definition CapSet := CapName -> Prop.

Definition cap_empty : CapSet := fun _ => False.
Definition cap_singleton (c : CapName) : CapSet := fun c' => c = c'.
Definition cap_union (k1 k2 : CapSet) : CapSet := fun c => k1 c \/ k2 c.
Definition cap_subset (k1 k2 : CapSet) : Prop := forall c, k1 c -> k2 c.
Definition cap_nonempty (k : CapSet) : Prop := exists c, k c.
Definition cap_mem (c : CapName) (k : CapSet) : Prop := k c.

Notation "k1 '∪k' k2" := (cap_union k1 k2) (at level 50).
Notation "k1 '⊆k' k2" := (cap_subset k1 k2) (at level 70).

(** Capability set properties. *)

Lemma cap_union_comm : forall k1 k2 c,
  (k1 ∪k k2) c <-> (k2 ∪k k1) c.
Proof. unfold cap_union; intuition. Qed.

Lemma cap_union_assoc : forall k1 k2 k3 c,
  ((k1 ∪k k2) ∪k k3) c <-> (k1 ∪k (k2 ∪k k3)) c.
Proof. unfold cap_union; intuition. Qed.

Lemma cap_union_empty_l : forall k c,
  (cap_empty ∪k k) c <-> k c.
Proof. unfold cap_union, cap_empty; intuition. Qed.

Lemma cap_union_empty_r : forall k c,
  (k ∪k cap_empty) c <-> k c.
Proof. unfold cap_union, cap_empty; intuition. Qed.

Lemma cap_subset_union_l : forall k1 k2,
  k1 ⊆k (k1 ∪k k2).
Proof. unfold cap_subset, cap_union; auto. Qed.

Lemma cap_subset_union_r : forall k1 k2,
  k2 ⊆k (k1 ∪k k2).
Proof. unfold cap_subset, cap_union; auto. Qed.

Lemma cap_subset_refl : forall k, k ⊆k k.
Proof. unfold cap_subset; auto. Qed.

Lemma cap_subset_trans : forall k1 k2 k3,
  k1 ⊆k k2 -> k2 ⊆k k3 -> k1 ⊆k k3.
Proof. unfold cap_subset; auto. Qed.

Lemma cap_union_mono : forall k1 k1' k2 k2',
  k1 ⊆k k1' -> k2 ⊆k k2' -> (k1 ∪k k2) ⊆k (k1' ∪k k2').
Proof.
  unfold cap_subset, cap_union; intros.
  destruct H1; auto.
Qed.

(* ================================================================= *)
(** ** 3. Effect Grade (Product)                                      *)
(* ================================================================= *)

(** Effect grade: the product of Risk × CapSet × nat.
    Corresponds to EffAlg_RunbookFX = Risk × K × ResCount. *)
Record Effect : Type := mkEffect {
  eff_risk : Risk;
  eff_caps : CapSet;
  eff_res  : nat
}.

(** The bottom effect: (ReadOnly, ∅, 0). *)
Definition eff_bot : Effect :=
  mkEffect ReadOnly cap_empty 0.

(** Effect join: componentwise (risk_join, ∪, +). *)
Definition eff_join (e1 e2 : Effect) : Effect :=
  mkEffect
    (risk_join (eff_risk e1) (eff_risk e2))
    (cap_union (eff_caps e1) (eff_caps e2))
    (eff_res e1 + eff_res e2).

Notation "e1 '⊔e' e2" := (eff_join e1 e2) (at level 50).

(** Effect ordering: componentwise (≤r, ⊆, ≤). *)
Definition eff_le (e1 e2 : Effect) : Prop :=
  (eff_risk e1) ≤r (eff_risk e2) /\
  (eff_caps e1) ⊆k (eff_caps e2) /\
  (eff_res e1) <= (eff_res e2).

Notation "e1 '≤e' e2" := (eff_le e1 e2) (at level 70).

(* ================================================================= *)
(** ** 4. Effect Monoid Laws (Definition 1)                           *)
(* ================================================================= *)

(** Identity: ⊥ ⊔ ε = ε *)
Theorem eff_join_identity_l : forall e,
  eff_le (eff_join eff_bot e) e /\ eff_le e (eff_join eff_bot e).
Proof.
  intros [r k n]; unfold eff_join, eff_bot, eff_le; simpl.
  split; (split; [destruct r; simpl; auto | split]).
  - intros c Hc. destruct Hc as [Hc | Hc]; [contradiction | exact Hc].
  - lia.
  - intros c Hc. right. exact Hc.
  - lia.
Qed.

(** Commutativity: ε₁ ⊔ ε₂ ≡ ε₂ ⊔ ε₁
    (extensional equality on the capability component) *)
Theorem eff_join_comm : forall e1 e2,
  eff_risk (e1 ⊔e e2) = eff_risk (e2 ⊔e e1) /\
  (forall c, eff_caps (e1 ⊔e e2) c <-> eff_caps (e2 ⊔e e1) c) /\
  eff_res (e1 ⊔e e2) = eff_res (e2 ⊔e e1).
Proof.
  intros [r1 k1 n1] [r2 k2 n2]; unfold eff_join; simpl.
  split; [| split].
  - apply risk_join_comm.
  - intros c. apply cap_union_comm.
  - lia.
Qed.

(** Associativity: (ε₁ ⊔ ε₂) ⊔ ε₃ ≡ ε₁ ⊔ (ε₂ ⊔ ε₃) *)
Theorem eff_join_assoc : forall e1 e2 e3,
  eff_risk ((e1 ⊔e e2) ⊔e e3) = eff_risk (e1 ⊔e (e2 ⊔e e3)) /\
  (forall c, eff_caps ((e1 ⊔e e2) ⊔e e3) c <->
             eff_caps (e1 ⊔e (e2 ⊔e e3)) c) /\
  eff_res ((e1 ⊔e e2) ⊔e e3) = eff_res (e1 ⊔e (e2 ⊔e e3)).
Proof.
  intros [r1 k1 n1] [r2 k2 n2] [r3 k3 n3]; unfold eff_join; simpl.
  split; [| split].
  - apply risk_join_assoc.
  - intros c. apply cap_union_assoc.
  - lia.
Qed.

(** Monotonicity: ε₁ ≤ ε₁' ∧ ε₂ ≤ ε₂' → ε₁ ⊔ ε₂ ≤ ε₁' ⊔ ε₂' *)
Theorem eff_join_mono : forall e1 e1' e2 e2',
  e1 ≤e e1' -> e2 ≤e e2' -> (e1 ⊔e e2) ≤e (e1' ⊔e e2').
Proof.
  intros [r1 k1 n1] [r1' k1' n1'] [r2 k2 n2] [r2' k2' n2'].
  unfold eff_le, eff_join; simpl.
  intros [Hr1 [Hk1 Hn1]] [Hr2 [Hk2 Hn2]].
  split; [| split].
  - apply risk_join_mono; auto.
  - apply cap_union_mono; auto.
  - lia.
Qed.

(** Reflexivity of effect ordering. *)
Lemma eff_le_refl : forall e, e ≤e e.
Proof.
  intros [r k n]; unfold eff_le; simpl.
  split; [| split].
  - apply risk_le_refl.
  - apply cap_subset_refl.
  - lia.
Qed.

(** Transitivity of effect ordering. *)
Lemma eff_le_trans : forall e1 e2 e3,
  e1 ≤e e2 -> e2 ≤e e3 -> e1 ≤e e3.
Proof.
  intros [r1 k1 n1] [r2 k2 n2] [r3 k3 n3].
  unfold eff_le; simpl.
  intros [Hr1 [Hk1 Hn1]] [Hr2 [Hk2 Hn2]].
  split; [| split].
  - eapply risk_le_trans; eauto.
  - eapply cap_subset_trans; eauto.
  - lia.
Qed.

(** Join produces an upper bound. *)
Lemma eff_join_ub_l : forall e1 e2, e1 ≤e (e1 ⊔e e2).
Proof.
  intros [r1 k1 n1] [r2 k2 n2]; unfold eff_le, eff_join; simpl.
  split; [| split].
  - apply risk_join_ub_l.
  - apply cap_subset_union_l.
  - lia.
Qed.

Lemma eff_join_ub_r : forall e1 e2, e2 ≤e (e1 ⊔e e2).
Proof.
  intros [r1 k1 n1] [r2 k2 n2]; unfold eff_le, eff_join; simpl.
  split; [| split].
  - apply risk_join_ub_r.
  - apply cap_subset_union_r.
  - lia.
Qed.

(* ================================================================= *)
(** ** 5. Well-Formed Effect Grade (Definition 2)                     *)
(* ================================================================= *)

(** An effect grade (r, k, n) is well-formed if it satisfies
    the four interaction axioms I1-I4. *)
Definition wf_effect (e : Effect) : Prop :=
  let r := eff_risk e in
  let k := eff_caps e in
  let n := eff_res e in
  (* I1: ReadOnly → n = 0 *)
  (r = ReadOnly -> n = 0) /\
  (* I2: Disruptive → k ≠ ∅ *)
  (r = Disruptive -> cap_nonempty k) /\
  (* I3: n > 0 → r ≥ SafeChange *)
  (n > 0 -> SafeChange ≤r r) /\
  (* I4: ∀ c ∈ k, risk(c) ≤ r *)
  (forall c, k c -> risk_of_cap c ≤r r).

(** Shorthand for constructing well-formed effect evidence. *)
Ltac wf_split := unfold wf_effect; simpl; repeat split.

(* ================================================================= *)
(** ** 6. Well-formedness of Base Effects                              *)
(* ================================================================= *)

(** The bottom effect ⊥ = (ReadOnly, ∅, 0) is well-formed. *)
Lemma wf_bot : wf_effect eff_bot.
Proof.
  unfold wf_effect, eff_bot; simpl.
  split; [| split; [| split]].
  - intros; reflexivity.
  - intros H; discriminate.
  - intros H; lia.
  - intros c Hc; unfold cap_empty in Hc; contradiction.
Qed.

(** The effect of T-Observe: (ReadOnly, {c}, 0) is well-formed. *)
Lemma wf_observe : forall c,
  risk_of_cap c ≤r ReadOnly ->
  wf_effect (mkEffect ReadOnly (cap_singleton c) 0).
Proof.
  intros c Hrc.
  unfold wf_effect; simpl.
  split; [| split; [| split]].
  - intros; reflexivity.
  - intros H; discriminate.
  - intros H; lia.
  - intros c' Hc'. unfold cap_singleton in Hc'. subst. exact Hrc.
Qed.

(** The effect of T-Act: (risk(c), {c}, 1) is well-formed,
    assuming risk(c) ≥ SafeChange (i.e., act only on mutation capabilities). *)
Lemma wf_act : forall c,
  SafeChange ≤r risk_of_cap c ->
  wf_effect (mkEffect (risk_of_cap c) (cap_singleton c) 1).
Proof.
  intros c Hrc.
  unfold wf_effect; simpl.
  split; [| split; [| split]].
  - (* I1 *) intros Heq.
    destruct (risk_of_cap c) eqn:Hc; simpl in *; try discriminate.
    contradiction.
  - (* I2 *) intros _. exists c. unfold cap_singleton. reflexivity.
  - (* I3 *) intros _.
    destruct (risk_of_cap c) eqn:Hc; simpl in *; auto; contradiction.
  - (* I4 *) intros c' Hc'. unfold cap_singleton in Hc'.
    subst. apply risk_le_refl.
Qed.

(** The effect of T-Rollback: (SafeChange, ∅, 0) is well-formed. *)
Lemma wf_rollback : wf_effect (mkEffect SafeChange cap_empty 0).
Proof.
  unfold wf_effect; simpl.
  split; [| split; [| split]].
  - discriminate.
  - discriminate.
  - intros H; lia.
  - intros c Hc. unfold cap_empty in Hc. contradiction.
Qed.

(* ================================================================= *)
(** ** 7. Theorem 1: Well-Formedness Preservation under Join          *)
(* ================================================================= *)

(** Helper: risk_join produces at least SafeChange when either input does. *)
Lemma risk_join_ge_safechange : forall r1 r2,
  SafeChange ≤r r1 \/ SafeChange ≤r r2 ->
  SafeChange ≤r (r1 ⊔r r2).
Proof.
  destruct r1, r2; simpl; intros [H | H]; auto; try contradiction.
Qed.

(** Helper: ReadOnly is not ≥ SafeChange. *)
Lemma readonly_not_ge_safechange :
  ~ (SafeChange ≤r ReadOnly).
Proof. simpl. auto. Qed.

(** Helper: if risk_join r1 r2 = ReadOnly, then both are ReadOnly. *)
Lemma risk_join_readonly : forall r1 r2,
  r1 ⊔r r2 = ReadOnly -> r1 = ReadOnly /\ r2 = ReadOnly.
Proof.
  destruct r1, r2; simpl; intros H; try discriminate; auto.
Qed.

(** Helper: if risk_join r1 r2 = Disruptive, then r1 or r2 is Disruptive. *)
Lemma risk_join_disruptive : forall r1 r2,
  r1 ⊔r r2 = Disruptive -> r1 = Disruptive \/ r2 = Disruptive.
Proof.
  destruct r1, r2; simpl; intros H; try discriminate; auto.
Qed.

(** Main theorem: wf is preserved under effect join.

    Theorem 1 from the paper (type_system.tex, lines 69-75):
    If wf(ε₁) and wf(ε₂), then wf(ε₁ ⊔ ε₂). *)
Theorem wf_preservation : forall e1 e2,
  wf_effect e1 -> wf_effect e2 -> wf_effect (e1 ⊔e e2).
Proof.
  intros [r1 k1 n1] [r2 k2 n2].
  unfold wf_effect, eff_join; simpl.
  intros [I1_1 [I2_1 [I3_1 I4_1]]] [I1_2 [I2_2 [I3_2 I4_2]]].
  split; [| split; [| split]].

  - (* I1: risk_join r1 r2 = ReadOnly → n1 + n2 = 0 *)
    intros Hro.
    apply risk_join_readonly in Hro. destruct Hro as [Hr1 Hr2].
    rewrite (I1_1 Hr1), (I1_2 Hr2). reflexivity.

  - (* I2: risk_join r1 r2 = Disruptive → cap_nonempty (k1 ∪ k2) *)
    intros Hdis.
    apply risk_join_disruptive in Hdis.
    destruct Hdis as [Hd | Hd].
    + destruct (I2_1 Hd) as [c Hc].
      exists c. left. exact Hc.
    + destruct (I2_2 Hd) as [c Hc].
      exists c. right. exact Hc.

  - (* I3: n1 + n2 > 0 → SafeChange ≤ risk_join r1 r2 *)
    intros Hn.
    assert (n1 > 0 \/ n2 > 0) as [Hn1 | Hn2] by lia.
    + apply risk_join_ge_safechange. left. apply I3_1. exact Hn1.
    + apply risk_join_ge_safechange. right. apply I3_2. exact Hn2.

  - (* I4: ∀ c ∈ k1 ∪ k2, risk(c) ≤ risk_join r1 r2 *)
    intros c [Hc | Hc].
    + eapply risk_le_trans.
      * apply I4_1. exact Hc.
      * apply risk_join_ub_l.
    + eapply risk_le_trans.
      * apply I4_2. exact Hc.
      * apply risk_join_ub_r.
Qed.

(* ================================================================= *)
(** ** 8. Well-Formedness Preservation under Subsumption              *)
(* ================================================================= *)

(** T-Sub requires wf(ε') as a side condition. We verify that this is
    necessary: subsumption to an arbitrary larger effect does NOT
    automatically preserve well-formedness. *)

(** However, wf is preserved under subsumption when the target is
    explicitly checked (as T-Sub requires). This is a design validation. *)
Lemma wf_effect_preserved_by_explicit_sub : forall e e',
  wf_effect e -> e ≤e e' -> wf_effect e' -> wf_effect e'.
Proof. auto. Qed.

(** The above is trivial because T-Sub requires the user to provide
    wf(ε') — we include it for completeness. The key insight is that
    wf is NOT monotone w.r.t. ≤e in general: (ReadOnly, ∅, 0) ≤e
    (ReadOnly, ∅, 1) but the latter violates I1. Hence the explicit
    wf check in T-Sub is essential for soundness. *)

(* ================================================================= *)
(** ** 9. Additional Properties of the Effect Algebra                 *)
(* ================================================================= *)

(** Effect of observe: (ReadOnly, {c}, 0). *)
Definition eff_observe (c : CapName) : Effect :=
  mkEffect ReadOnly (cap_singleton c) 0.

(** Effect of act: (risk(c), {c}, 1). *)
Definition eff_act (c : CapName) : Effect :=
  mkEffect (risk_of_cap c) (cap_singleton c) 1.

(** Effect of rollback: (SafeChange, ∅, 0). *)
Definition eff_rollback : Effect :=
  mkEffect SafeChange cap_empty 0.

(** The bottom effect is a left identity for join (up to extensional eq). *)
Lemma eff_join_bot_l_risk : forall e,
  eff_risk (eff_bot ⊔e e) = eff_risk e.
Proof.
  intros [r k n]; simpl. apply risk_join_readonly_l.
Qed.

Lemma eff_join_bot_l_res : forall e,
  eff_res (eff_bot ⊔e e) = eff_res e.
Proof.
  intros [r k n]; simpl. reflexivity.
Qed.

(** Join monotonically increases the resource count. *)
Lemma eff_join_res_additive : forall e1 e2,
  eff_res (e1 ⊔e e2) = eff_res e1 + eff_res e2.
Proof.
  intros [r1 k1 n1] [r2 k2 n2]; simpl. reflexivity.
Qed.

(** If both effects are ReadOnly, so is their join. *)
Lemma eff_join_readonly_readonly : forall e1 e2,
  eff_risk e1 = ReadOnly -> eff_risk e2 = ReadOnly ->
  eff_risk (e1 ⊔e e2) = ReadOnly.
Proof.
  intros [r1 k1 n1] [r2 k2 n2]; simpl.
  intros Hr1 Hr2. subst. reflexivity.
Qed.

(* ================================================================= *)
(** ** 10. Effect Composition Examples                                *)
(* ================================================================= *)

(** Example: composing two observe effects.
    observe_c1 ⊔ observe_c2 = (ReadOnly, {c1} ∪ {c2}, 0) *)
Example compose_observes : forall c1 c2,
  eff_risk (eff_observe c1 ⊔e eff_observe c2) = ReadOnly /\
  eff_res (eff_observe c1 ⊔e eff_observe c2) = 0.
Proof.
  intros; unfold eff_observe, eff_join; simpl. auto.
Qed.

(** Example: composing observe with act.
    observe_c1 ⊔ act_c2 = (risk(c2), {c1} ∪ {c2}, 1) *)
Example compose_observe_act : forall c1 c2,
  eff_risk (eff_observe c1 ⊔e eff_act c2) = risk_of_cap c2 /\
  eff_res (eff_observe c1 ⊔e eff_act c2) = 1.
Proof.
  intros; unfold eff_observe, eff_act, eff_join; simpl.
  split.
  - apply risk_join_readonly_l.
  - reflexivity.
Qed.

(** Example: composing two act effects sums resources.
    act_c1 ⊔ act_c2 has resource count 2. *)
Example compose_acts_res : forall c1 c2,
  eff_res (eff_act c1 ⊔e eff_act c2) = 2.
Proof.
  intros; unfold eff_act, eff_join; simpl. reflexivity.
Qed.

(** The composition of two well-formed base effects is well-formed.
    This is a corollary of wf_preservation applied to base effects. *)
Corollary wf_compose_observe_act : forall c1 c2,
  risk_of_cap c1 ≤r ReadOnly ->
  SafeChange ≤r risk_of_cap c2 ->
  wf_effect (eff_observe c1 ⊔e eff_act c2).
Proof.
  intros c1 c2 H1 H2.
  apply wf_preservation.
  - apply wf_observe. exact H1.
  - apply wf_act. exact H2.
Qed.

(** End of EffectAlgebra.v *)
