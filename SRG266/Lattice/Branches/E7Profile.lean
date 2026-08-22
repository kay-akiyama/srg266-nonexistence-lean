/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.List.GetD
import SRG266.Hosts.E7CentroidTransport
import SRG266.Lattice.Branches.E7Histogram

/-!
# From centroid coordinates to the E7 trace filter

The `e7e7Plus` constructor of `SRG266.AuditedRank15HostCase` carries the membership
`(e7ComponentKey left, e7ComponentKey right) ∈ e7TraceFeasibleHistogramPairs`.
That list is cut out of the enumerated component keys by four successive
filters, and this file discharges all four from the geometry of a realization:

* norm complementarity `‖c₁‖² + ‖c₂‖² = 300` with `‖c₁‖²` even, because the
  centroid lies in the *even* lattice `E₇ ⊕ E₇`;
* `74 ≤ e7HistogramEligibleCount`, because the `220` generators occupy at least
  `74` distinct shell columns and every shell column is an eligible pair;
* scalar dynamic-programming feasibility, witnessed by the numbers of generators
  in each evaluation bin: their total is `220` and their moment is `11 ‖c₁‖²`,
  which is the left half of `∑_B v_B = 11 c`;
* the trace range `38 ≤ ‖c₁‖² ≤ 262`, which is supplied by the caller.

The arithmetic bound keeps every minuscule
evaluation inside the `43` histogram bins: for a sum-zero eight-vector `y`,
`2 (y_a + y_b)² ≤ 3 ∑ y²`, so `‖c₁‖² ≤ 300` gives `|⟨c₁, w⟩| ≤ 21` on the nose.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

/-- The squared norm recorded by a component key is the norm of the underlying
`E₇` vector. -/
theorem e7ComponentNorm_spec (p : Array ℤ) (hsize : p.size = 8) {m : ℤ} (hm : 0 ≤ m)
    (h : ∑ i, (e7ComponentEnumerationProfile p i) ^ 2 = 4 * m) :
    ((e7ComponentNorm p : ℕ) : ℤ) = m := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := e7Profile_eq_toArray p hsize
  have hsum : a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4 + a5 * a5 + a6 * a6 +
      a7 * a7 = 4 * m := by
    rw [← h, Fin.sum_univ_eight]
    show _ = (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 + a4 ^ 2 + a5 ^ 2 + a6 ^ 2 + a7 ^ 2)
    ring
  rw [e7ComponentNorm_eq_of_coordinates, e7FastNormOf, hsum]
  omega

/-! ## Minuscule evaluations of a profile -/

/-- Pairing a coordinate vector against a `0/±1`-patterned sign vector. -/
private theorem integerDot_pattern (y : Fin 8 → ℤ) (S : Finset (Fin 8)) (v : Fin 8 → ℤ)
    (e : ℤ) (hv : ∀ i, v i = e * (if i ∈ S then 3 else -1)) :
    integerDot y v = e * (4 * (∑ i ∈ S, y i) - ∑ i, y i) := by
  classical
  have hpoint : ∀ i, y i * v i = e * (4 * (if i ∈ S then y i else 0) - y i) := by
    intro i
    rw [hv i]
    by_cases hi : i ∈ S
    · rw [if_pos hi, if_pos hi]; ring
    · rw [if_neg hi, if_neg hi]; ring
  have hmem : ∑ i, (if i ∈ S then y i else 0) = ∑ i ∈ S, y i := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_mem_eq_inter,
      Finset.univ_inter]
  rw [integerDot, Finset.sum_congr rfl fun i _ => hpoint i, ← Finset.mul_sum,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hmem]

/-- **Pairing against a minuscule weight sees only its coordinate pair.**  Up to
the sign of the weight, `⟨y, w⟩ = 4 (y_a + y_b) - ∑ y`. -/
theorem integerDot_e7Weight4 (y : Fin 8 → ℤ) (w : E7WeightIndex) :
    integerDot y (e7Weight4 w) = 4 * (∑ i ∈ e7PairSet w.2, y i) - ∑ i, y i ∨
      integerDot y (e7Weight4 w) = -(4 * (∑ i ∈ e7PairSet w.2, y i) - ∑ i, y i) := by
  rcases Bool.eq_false_or_eq_true w.1 with hb | hb
  · refine Or.inr ?_
    rw [integerDot_pattern y (e7PairSet w.2) _ (-1) fun i => ?_]
    · ring
    · rw [e7Weight4_apply w i, hb]
      by_cases hi : i ∈ e7PairSet w.2 <;> simp [hi]
  · refine Or.inl ?_
    rw [integerDot_pattern y (e7PairSet w.2) _ 1 fun i => ?_]
    · ring
    · rw [e7Weight4_apply w i, hb]
      by_cases hi : i ∈ e7PairSet w.2 <;> simp [hi]

/-- The pair sum of a minuscule weight, in the two coordinates it selects. -/
theorem sum_e7PairSet (y : Fin 8 → ℤ) (t : E7PairIndex) :
    ∑ i ∈ e7PairSet t, y i = y (e7Pairs.get t).1 + y (e7Pairs.get t).2 :=
  Finset.sum_pair (e7Pairs_get_ne t)

/-- **The Cauchy--Schwarz bound behind the `43` histogram bins.**  For a
sum-zero eight-vector the sum of two coordinates is controlled by the norm:
`2 (y_a + y_b)² ≤ 3 ∑ y²`.  At `∑ y² ≤ 1200` this is `|y_a + y_b| ≤ 42`. -/
theorem two_mul_pair_sq_le (y : Fin 8 → ℤ) (hsum : ∑ i, y i = 0) {a b : Fin 8}
    (hab : a ≠ b) : 2 * (y a + y b) ^ 2 ≤ 3 * ∑ i, (y i) ^ 2 := by
  classical
  set T : Finset (Fin 8) := (Finset.univ : Finset (Fin 8)) \ {a, b} with hT
  have hsub : ({a, b} : Finset (Fin 8)) ⊆ Finset.univ := Finset.subset_univ _
  have hcardT : T.card = 6 := by
    rw [hT, Finset.card_sdiff, Finset.inter_univ, Finset.card_pair hab]
    simp
  have hsplit : ∀ f : Fin 8 → ℤ, (∑ i ∈ T, f i) + (f a + f b) = ∑ i, f i := by
    intro f
    rw [← Finset.sum_pair hab (f := f), hT]
    exact Finset.sum_sdiff hsub
  have hsum' := hsplit y
  have hsq' := hsplit fun i => (y i) ^ 2
  have hcs : (∑ i ∈ T, y i) ^ 2 ≤ (T.card : ℤ) * ∑ i ∈ T, (y i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hcardT] at hcs
  push_cast at hcs
  have hpair : (y a + y b) ^ 2 ≤ 2 * ((y a) ^ 2 + (y b) ^ 2) := by nlinarith [sq_nonneg (y a - y b)]
  have hneg : ∑ i ∈ T, y i = -(y a + y b) := by omega
  rw [hneg] at hcs
  nlinarith [hcs, hpair, hsq']

variable {p₁ p₂ : Array ℤ}

/-- Every minuscule evaluation of a profile of norm at most `300` lands in the
`43` histogram bins. -/
theorem e7ComponentEvaluation_bounds (p : Array ℤ)
    (hsum : ∑ i, e7ComponentEnumerationProfile p i = 0)
    (hsq : ∑ i, (e7ComponentEnumerationProfile p i) ^ 2 ≤ 1200) (w : E7WeightIndex) :
    -21 ≤ e7ComponentEvaluation p w ∧ e7ComponentEvaluation p w ≤ 21 := by
  set y := e7ComponentEnumerationProfile p with hy
  have hdot := integerDot_e7Weight4 y w
  rw [sum_e7PairSet y w.2, hsum] at hdot
  have hbound := two_mul_pair_sq_le y hsum (e7Pairs_get_ne w.2)
  have habs : -42 ≤ y (e7Pairs.get w.2).1 + y (e7Pairs.get w.2).2 ∧
      y (e7Pairs.get w.2).1 + y (e7Pairs.get w.2).2 ≤ 42 := by
    constructor <;> nlinarith [hbound, hsq]
  rw [e7ComponentEvaluation, ← hy]
  omega

/-- Minuscule evaluations of a same-parity profile are exact: the pairing is a
multiple of eight. -/
theorem eight_mul_e7ComponentEvaluation (p : Array ℤ)
    (hsum : ∑ i, e7ComponentEnumerationProfile p i = 0)
    (hpar : ∀ i j, e7ComponentEnumerationProfile p i % 2 =
      e7ComponentEnumerationProfile p j % 2) (w : E7WeightIndex) :
    8 * e7ComponentEvaluation p w =
      integerDot (e7ComponentEnumerationProfile p) (e7Weight4 w) := by
  set y := e7ComponentEnumerationProfile p with hy
  have hdot := integerDot_e7Weight4 y w
  rw [sum_e7PairSet y w.2, hsum] at hdot
  have hparity := hpar (e7Pairs.get w.2).1 (e7Pairs.get w.2).2
  obtain ⟨j, hj⟩ : (2 : ℤ) ∣ (y (e7Pairs.get w.2).1 + y (e7Pairs.get w.2).2) := by omega
  have hdvd : (8 : ℤ) ∣ integerDot y (e7Weight4 w) := by
    rcases hdot with h | h
    · exact ⟨j, by omega⟩
    · exact ⟨-j, by omega⟩
  obtain ⟨k, hk⟩ := hdvd
  rw [e7ComponentEvaluation, ← hy, hk, Int.mul_ediv_cancel_left _ (by norm_num)]

/-- **Eligibility is the bin equation.**  Bin `k` on the left meets bin `57 - k`
on the right exactly when the two minuscule evaluations sum to `15`. -/
theorem e7Eligible_iff_bin (hsum₁ : ∑ i, e7ComponentEnumerationProfile p₁ i = 0)
    (hsum₂ : ∑ i, e7ComponentEnumerationProfile p₂ i = 0)
    (hpar₁ : ∀ i j, e7ComponentEnumerationProfile p₁ i % 2 =
      e7ComponentEnumerationProfile p₁ j % 2)
    (hpar₂ : ∀ i j, e7ComponentEnumerationProfile p₂ i % 2 =
      e7ComponentEnumerationProfile p₂ j % 2)
    (hsq₁ : ∑ i, (e7ComponentEnumerationProfile p₁ i) ^ 2 ≤ 1200)
    (hsq₂ : ∑ i, (e7ComponentEnumerationProfile p₂ i) ^ 2 ≤ 1200)
    (w : E7ShellIndex) :
    e7Eligible (e7ComponentEnumerationProfile p₁) (e7ComponentEnumerationProfile p₂) w ↔
      e7Bin p₁ w.1 + e7Bin p₂ w.2 = 57 := by
  have hleft := eight_mul_e7ComponentEvaluation p₁ hsum₁ hpar₁ w.1
  have hright := eight_mul_e7ComponentEvaluation p₂ hsum₂ hpar₂ w.2
  have hlb := e7ComponentEvaluation_bounds p₁ hsum₁ hsq₁ w.1
  have hrb := e7ComponentEvaluation_bounds p₂ hsum₂ hsq₂ w.2
  rw [e7Bin, e7Bin, e7Eligible]
  omega

theorem e7Bin_lt (p : Array ℤ) (hsum : ∑ i, e7ComponentEnumerationProfile p i = 0)
    (hsq : ∑ i, (e7ComponentEnumerationProfile p i) ^ 2 ≤ 1200) (w : E7WeightIndex) :
    e7Bin p w < 43 := by
  have h := e7ComponentEvaluation_bounds p hsum hsq w
  rw [e7Bin]
  omega

/-! ## Feeding the scalar dynamic program -/

private theorem sum_map_range {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    ∀ n : ℕ, ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

private theorem forall₂_map_map {α β γ : Type*} (R : β → γ → Prop) (f : α → β) (g : α → γ)
    (l : List α) (h : ∀ a ∈ l, R (f a) (g a)) : List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a t ih =>
      exact List.Forall₂.cons (h a List.mem_cons_self)
        (ih fun b hb => h b (List.mem_cons_of_mem a hb))

/-- Applying a list of category choices accumulates the usages and the weighted
moment. -/
theorem e7ScalarApplyChoices_map {α : Type*} (f : α → ℤ × ℕ) (g : α → ℕ) :
    ∀ (l : List α) (state : E7ScalarState),
      e7ScalarApplyChoices state (l.map f) (l.map g) =
        { used := state.used + (l.map g).sum
          value := state.value + (l.map fun a => (f a).1 * (g a : ℤ)).sum } := by
  intro l
  induction l with
  | nil => intro state; simp [e7ScalarApplyChoices]
  | cons a t ih =>
      intro state
      rw [List.map_cons, List.map_cons, e7ScalarApplyChoices, ih]
      simp only [List.map_cons, List.sum_cons, E7ScalarState.mk.injEq]
      constructor
      · omega
      · ring

theorem e7ComponentKey_histogram (p : Array ℤ) :
    (e7ComponentKey p).histogram = e7ComponentHistogram p := by
  simp only [e7ComponentKey]

theorem e7ComponentKey_norm' (p : Array ℤ) :
    (e7ComponentKey p).norm = e7ComponentNorm p := by
  simp only [e7ComponentKey]

/-- **The scalar dynamic program accepts a bin-count witness.**  A family of
category usages bounded by the capacities, of total `220` and of left moment
`11 ‖c₁‖²`, is exactly what `SRG266.e7ScalarDPFeasible` searches for. -/
theorem e7ScalarDPFeasible_of_binCounts (left right : E7ComponentKey) (mult : ℕ → ℕ)
    (hcap : ∀ k, k < 43 →
      mult k ≤ 3 * left.histogram.getD k 0 * right.histogram.getD (57 - k) 0)
    (htotal : ∑ k ∈ Finset.range 43, mult k = 220)
    (hmoment : ∑ k ∈ Finset.range 43, ((k : ℤ) - 21) * (mult k : ℤ) =
      11 * (left.norm : ℤ)) :
    e7ScalarDPFeasible (left, right) = true := by
  refine e7ScalarDPFeasible_of_choices _ _ ((List.range 43).map mult) ?_ ?_ ?_
  · rw [e7ScalarCategories]
    exact forall₂_map_map _ _ _ _ fun k hk => hcap k (List.mem_range.mp hk)
  · rw [sum_map_range mult 43, htotal]
  · rw [e7ScalarCategories, e7ScalarApplyChoices_map, e7ScalarTarget,
      sum_map_range mult 43, htotal,
      sum_map_range (fun k => ((k : ℤ) - 21) * (mult k : ℤ)) 43, hmoment]
    simp

/-! ## The trace filter of a realization -/

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **The four filters of `e7TraceFeasibleHistogramPairs`, discharged.**  A
direct realization at two enumerated component profiles whose norms satisfy the
complementarity, parity and trace conditions has a trace-feasible key pair. -/
theorem e7TraceFeasible_of_realization (hG : IsHypothetical G) (x : V)
    {n₁ n₂ : ℤ} (hsize₁ : p₁.size = 8) (hsize₂ : p₂.size = 8)
    (hmem₁ : p₁ ∈ e7EnumeratedComponentProfiles)
    (hmem₂ : p₂ ∈ e7EnumeratedComponentProfiles)
    (hsum₁ : ∑ i, e7ComponentEnumerationProfile p₁ i = 0)
    (hsum₂ : ∑ i, e7ComponentEnumerationProfile p₂ i = 0)
    (hpar₁ : ∀ i j, e7ComponentEnumerationProfile p₁ i % 2 =
      e7ComponentEnumerationProfile p₁ j % 2)
    (hpar₂ : ∀ i j, e7ComponentEnumerationProfile p₂ i % 2 =
      e7ComponentEnumerationProfile p₂ j % 2)
    (hnorm₁ : ∑ i, (e7ComponentEnumerationProfile p₁ i) ^ 2 = 4 * n₁)
    (hnorm₂ : ∑ i, (e7ComponentEnumerationProfile p₂ i) ^ 2 = 4 * n₂)
    (heven : (2 : ℤ) ∣ n₁) (htotal : n₁ + n₂ = 300) (hlow : 38 ≤ n₁) (hhigh : n₁ ≤ 262)
    (realization : E7CentroidShellGramRealization G x
      (e7ComponentEnumerationProfile p₁) (e7ComponentEnumerationProfile p₂)) :
    (e7ComponentKey p₁, e7ComponentKey p₂) ∈ e7TraceFeasibleHistogramPairs := by
  classical
  have hnn₂ : (0 : ℤ) ≤ 4 * n₂ := by
    rw [← hnorm₂]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq₁ : ∑ i, (e7ComponentEnumerationProfile p₁ i) ^ 2 ≤ 1200 := by
    rw [hnorm₁]; omega
  have hsq₂ : ∑ i, (e7ComponentEnumerationProfile p₂ i) ^ 2 ≤ 1200 := by
    rw [hnorm₂]; omega
  have hr₁ : ∀ w, e7Bin p₁ w < 43 := e7Bin_lt p₁ hsum₁ hsq₁
  have hr₂ : ∀ w, e7Bin p₂ w < 43 := e7Bin_lt p₂ hsum₂ hsq₂
  have heq : ∀ w : E7ShellIndex,
      e7Eligible (e7ComponentEnumerationProfile p₁) (e7ComponentEnumerationProfile p₂) w ↔
        e7Bin p₁ w.1 + e7Bin p₂ w.2 = 57 :=
    e7Eligible_iff_bin hsum₁ hsum₂ hpar₁ hpar₂ hsq₁ hsq₂
  -- the two component norms
  have hkey₁ : ((e7ComponentKey p₁).norm : ℤ) = n₁ :=
    e7ComponentNorm_spec p₁ hsize₁ (by omega) hnorm₁
  have hkey₂ : ((e7ComponentKey p₂).norm : ℤ) = n₂ :=
    e7ComponentNorm_spec p₂ hsize₂ (by omega) hnorm₂
  -- filter one: norm complementarity
  have hcomplementary : (e7ComponentKey p₁, e7ComponentKey p₂) ∈
      e7NormComplementaryHistogramPairs := by
    refine pair_mem_e7NormComplementaryHistogramPairs _ _
      (e7ComponentKey_mem_of_profile_mem p₁ hmem₁)
      (e7ComponentKey_mem_of_profile_mem p₂ hmem₂) ?_ ?_
    · obtain ⟨k, hk⟩ := heven
      refine ⟨k.toNat, ?_⟩
      omega
    · omega
  -- filter two: at least seventy-four eligible columns
  have hcount : 74 ≤ e7HistogramEligibleCount (e7ComponentKey p₁) (e7ComponentKey p₂) := by
    have hsupport := (realization.toFiniteShell G).seventyFour_le_support_card G hG x
    have hle := Finset.card_le_univ (Finset.univ.filter fun s =>
      0 < (realization.toFiniteShell G).multiplicity G s)
    rw [← card_e7EligibleIndex_eq_histogramEligibleCount p₁ p₂ hr₁ hr₂ heq]
    omega
  have heligible : (e7ComponentKey p₁, e7ComponentKey p₂) ∈ e7EligibleHistogramPairs :=
    pair_mem_e7EligibleHistogramPairs _ _ hcomplementary hcount
  -- filter three: scalar dynamic-programming feasibility
  have hbinB : ∀ B : SecondSubconstituent G x,
      e7Bin p₁ (realization.shell B).1.1 ∈ Finset.range 43 := fun B =>
    Finset.mem_range.mpr (hr₁ _)
  obtain ⟨mult, hmult⟩ : ∃ mult : ℕ → ℕ, ∀ k, mult k =
      (Finset.univ.filter fun B : SecondSubconstituent G x =>
        e7Bin p₁ (realization.shell B).1.1 = k).card := ⟨_, fun _ => rfl⟩
  have htotalMult : ∑ k ∈ Finset.range 43, mult k = 220 := by
    rw [Finset.sum_congr rfl fun k _ => hmult k,
      ← Finset.card_eq_sum_card_fiberwise fun B _ => hbinB B, Finset.card_univ,
      secondSubconstituent_card G hG x]
  have hcapacity : ∀ k ∈ Finset.range 43,
      mult k ≤ 3 * ((e7BinFinset p₁ k).card * (e7BinFinset p₂ (57 - k)).card) := by
    intro k hk
    have hk' : k < 43 := Finset.mem_range.mp hk
    set t : Finset (E7EligibleIndex (e7ComponentEnumerationProfile p₁)
      (e7ComponentEnumerationProfile p₂)) :=
      Finset.univ.filter fun u => e7Bin p₁ u.1.1 = k with ht
    have hfiber : ∑ u ∈ t, (realization.toFiniteShell G).multiplicity G u =
        (Finset.univ.filter fun B => realization.shell B ∈ t).card :=
      Finset.sum_card_fiberwise_eq_card_filter _ _ _
    have hfilter : (Finset.univ.filter fun B : SecondSubconstituent G x =>
        realization.shell B ∈ t) =
          Finset.univ.filter fun B : SecondSubconstituent G x =>
            e7Bin p₁ (realization.shell B).1.1 = k := by
      refine Finset.filter_congr fun B _ => ?_
      simp [ht]
    have hbound : ∑ u ∈ t, (realization.toFiniteShell G).multiplicity G u ≤ 3 * t.card := by
      calc ∑ u ∈ t, (realization.toFiniteShell G).multiplicity G u ≤ ∑ _u ∈ t, 3 :=
            Finset.sum_le_sum fun u _ =>
              (realization.toFiniteShell G).multiplicity_le_three G hG x u
        _ = 3 * t.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    rw [hfilter] at hfiber
    rw [hmult k, ← hfiber, ht]
    exact le_trans hbound
      (Nat.mul_le_mul_left 3
        (le_of_eq (card_e7EligibleIndex_bin_fiber p₁ p₂ heq k hk')))
  have hmoment : ∑ k ∈ Finset.range 43, ((k : ℤ) - 21) * (mult k : ℤ) = 11 * n₁ := by
    have hfiberwise : ∑ k ∈ Finset.range 43,
        ∑ B ∈ Finset.univ.filter fun B : SecondSubconstituent G x =>
          e7Bin p₁ (realization.shell B).1.1 = k,
          ((e7Bin p₁ (realization.shell B).1.1 : ℤ) - 21) =
        ∑ B : SecondSubconstituent G x, ((e7Bin p₁ (realization.shell B).1.1 : ℤ) - 21) :=
      Finset.sum_fiberwise_of_maps_to (fun B _ => hbinB B) _
    have hconst : ∀ k ∈ Finset.range 43,
        ∑ B ∈ Finset.univ.filter fun B : SecondSubconstituent G x =>
          e7Bin p₁ (realization.shell B).1.1 = k,
          ((e7Bin p₁ (realization.shell B).1.1 : ℤ) - 21) =
        ((k : ℤ) - 21) * (mult k : ℤ) := by
      intro k _
      rw [Finset.sum_congr rfl fun B hB => by
        rw [(Finset.mem_filter.mp hB).2], Finset.sum_const, nsmul_eq_mul, hmult k, mul_comm]
    rw [Finset.sum_congr rfl hconst] at hfiberwise
    rw [hfiberwise]
    -- the moment of the evaluations is `11 ‖c₁‖²`
    have hev : ∀ B : SecondSubconstituent G x,
        ((e7Bin p₁ (realization.shell B).1.1 : ℤ) - 21) =
          e7ComponentEvaluation p₁ (realization.shell B).1.1 := by
      intro B
      have h := e7ComponentEvaluation_bounds p₁ hsum₁ hsq₁ (realization.shell B).1.1
      rw [e7Bin]
      omega
    have hdot : ∀ B : SecondSubconstituent G x,
        8 * e7ComponentEvaluation p₁ (realization.shell B).1.1 =
          ∑ i, e7ComponentEnumerationProfile p₁ i * e7Weight4 (realization.shell B).1.1 i := by
      intro B
      exact eight_mul_e7ComponentEvaluation p₁ hsum₁ hpar₁ (realization.shell B).1.1
    have hsumdot : ∑ B : SecondSubconstituent G x,
        (8 : ℤ) * e7ComponentEvaluation p₁ (realization.shell B).1.1 =
          8 * (11 * n₁) := by
      rw [Finset.sum_congr rfl fun B _ => hdot B, Finset.sum_comm]
      have hcent : ∀ i, ∑ B : SecondSubconstituent G x,
          e7ComponentEnumerationProfile p₁ i * e7Weight4 (realization.shell B).1.1 i =
            e7ComponentEnumerationProfile p₁ i * (22 * e7ComponentEnumerationProfile p₁ i) := by
        intro i
        rw [← Finset.mul_sum, realization.leftCentroid i]
      rw [Finset.sum_congr rfl fun i _ => hcent i]
      have : ∑ i, e7ComponentEnumerationProfile p₁ i *
          (22 * e7ComponentEnumerationProfile p₁ i) =
            22 * ∑ i, (e7ComponentEnumerationProfile p₁ i) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, hnorm₁]
      ring
    rw [Finset.sum_congr rfl fun B _ => hev B]
    have := Finset.mul_sum (Finset.univ : Finset (SecondSubconstituent G x))
      (fun B => e7ComponentEvaluation p₁ (realization.shell B).1.1) (8 : ℤ)
    omega
  have hfeasible : e7ScalarDPFeasible (e7ComponentKey p₁, e7ComponentKey p₂) = true := by
    refine e7ScalarDPFeasible_of_binCounts _ _ mult (fun k hk => ?_) htotalMult ?_
    · rw [e7ComponentKey_histogram, e7ComponentKey_histogram,
        e7ComponentHistogram_getD p₁ hr₁ k, e7ComponentHistogram_getD p₂ hr₂ (57 - k),
        Nat.mul_assoc]
      exact hcapacity k (Finset.mem_range.mpr hk)
    · rw [hmoment, ← hkey₁]
  have hscalar : (e7ComponentKey p₁, e7ComponentKey p₂) ∈ e7ScalarFeasibleHistogramPairs :=
    pair_mem_e7ScalarFeasibleHistogramPairs _ heligible hfeasible
  have hnormlow : 38 ≤ (e7ComponentKey p₁).norm := by omega
  have hnormhigh : (e7ComponentKey p₁).norm ≤ 262 := by omega
  exact pair_mem_e7TraceFeasibleHistogramPairs _ hscalar hnormlow hnormhigh

end Lattice
end SRG266
