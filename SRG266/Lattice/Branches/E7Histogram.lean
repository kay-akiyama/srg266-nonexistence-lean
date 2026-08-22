/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7CodeKeyArithmetic
import SRG266.Hosts.E7E7Plus
import SRG266.Hosts.E7FastComponentKey
import SRG266.Hosts.E7ScalarDP
import SRG266.Lattice.Branches.E7Weight

/-!
# The evaluation histogram counts minuscule weights

`SRG266.e7ComponentHistogram` folds `56` unit increments into a `43`-bin
`Array ℕ`, and `SRG266.e7HistogramEligibleCount` convolves two such histograms.
Both are executable devices; this file identifies them with the counting
statements the `(E₇ ⊕ E₇)⁺` branch actually has:

* `SRG266.Lattice.e7ComponentHistogram_getD` — bin `k` of the histogram is the
  number of minuscule weights whose evaluation lands in bin `k`;
* `SRG266.Lattice.card_e7EligibleIndex_eq_histogramEligibleCount` — the
  convolution `∑ₖ h₁(k) h₂(57 - k)` is the cardinality of
  `SRG266.E7EligibleIndex`, because bin `k` on the left and bin `57 - k` on the
  right is exactly `⟨c₁, w₁⟩ + ⟨c₂, w₂⟩ = 15`;
* `SRG266.Lattice.card_e7EligibleIndex_bin_fiber` — the same count restricted to
  one left bin, which is the capacity the scalar dynamic program of
  `SRG266/Hosts/E7ScalarDP.lean` allots to its `k`-th category.

The whole file is `Array`-free after the first section: the packed-code
machinery of `SRG266/Hosts/E7ComponentCode.lean` already proves that folding
unit increments into the bin array and into the base-`64` digits of a natural
number agree, so bin `k` is a digit, and a digit of a sum of powers is a count.

Both statements are conditional on every evaluation lying in `[-21, 21]`, i.e.
on every bin index being below `43`.  That is not automatic — it is the
Cauchy--Schwarz bound `2 ⟨y, w⟩² ≤ 3 ‖y‖² ‖w‖²` at `‖y‖² ≤ 300`, supplied by the
branch.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

set_option maxRecDepth 40000

/-! ## Digits of a sum of packed increments -/

/-- One packed increment raises the addressed digit by one and leaves every
other digit alone.  This is the equality behind
`SRG266.e7CodeDigit_add_binWeight_le`. -/
theorem e7CodeDigit_add_binWeight (c b k : ℕ) (hk : k < 43)
    (hc : c / e7CodeBase ^ b % e7CodeBase + 1 < e7CodeBase) :
    (c + e7BinWeight b) / e7CodeBase ^ k % e7CodeBase =
      c / e7CodeBase ^ k % e7CodeBase + (if b = k then 1 else 0) := by
  by_cases hb : b < 43
  · have hw : e7BinWeight b = e7CodeBase ^ b := by simp [e7BinWeight, hb]
    rw [hw]
    set n := b + k + 1 with hn
    have hkn : k < n := by omega
    have hlist := e7CodeDigits_add_pow n c b hc
    have hleft : (c + e7CodeBase ^ b) / e7CodeBase ^ k % e7CodeBase =
        ((e7CodeDigits n c).set b ((e7CodeDigits n c).getD b 0 + 1)).getD k 0 := by
      rw [← hlist, e7CodeDigits_getD n _ k hkn]
    rw [hleft]
    by_cases hkb : b = k
    · subst hkb
      have hset :
          ((e7CodeDigits n c).set b ((e7CodeDigits n c).getD b 0 + 1)).getD b 0 =
            (e7CodeDigits n c).getD b 0 + 1 := by
        show (((e7CodeDigits n c).set b ((e7CodeDigits n c).getD b 0 + 1))[b]?).getD 0 = _
        rw [List.getElem?_set_self (by rw [e7CodeDigits_length]; omega)]
        rfl
      rw [hset, e7CodeDigits_getD n c b (by omega), if_pos rfl]
    · have hset :
          ((e7CodeDigits n c).set b ((e7CodeDigits n c).getD b 0 + 1)).getD k 0 =
            (e7CodeDigits n c).getD k 0 := by
        show (((e7CodeDigits n c).set b ((e7CodeDigits n c).getD b 0 + 1))[k]?).getD 0 = _
        rw [List.getElem?_set_ne (by omega)]
        rfl
      rw [hset, e7CodeDigits_getD n c k hkn, if_neg hkb, Nat.add_zero]
  · have hw : e7BinWeight b = 0 := by simp [e7BinWeight, hb]
    rw [hw, Nat.add_zero, if_neg (by omega), Nat.add_zero]

/-- Every digit of a packed sum of increments is bounded by the number of
increments. -/
theorem e7BinWeight_sum_digit_le :
    ∀ (l : List ℕ), l.length < 63 → ∀ k : ℕ,
      (l.map e7BinWeight).sum / e7CodeBase ^ k % e7CodeBase ≤ l.length := by
  intro l
  induction l with
  | nil => intro _ k; simp
  | cons b t ih =>
      intro hlen k
      have htail : t.length < 63 := by
        simp only [List.length_cons] at hlen
        omega
      have hsum : ((b :: t).map e7BinWeight).sum =
          (t.map e7BinWeight).sum + e7BinWeight b := by
        simp only [List.map_cons, List.sum_cons]
        omega
      have hc : (t.map e7BinWeight).sum / e7CodeBase ^ b % e7CodeBase + 1 < e7CodeBase := by
        have hbase : e7CodeBase = 64 := rfl
        have := ih htail b
        omega
      have hstep := e7CodeDigit_add_binWeight_le (t.map e7BinWeight).sum b k hc
      have := ih htail k
      rw [hsum]
      simp only [List.length_cons]
      omega

/-- **A digit of a packed sum of increments is a count.** -/
theorem e7BinWeight_sum_digit :
    ∀ (l : List ℕ), l.length < 63 → ∀ k : ℕ, k < 43 →
      (l.map e7BinWeight).sum / e7CodeBase ^ k % e7CodeBase = l.count k := by
  intro l
  induction l with
  | nil => intro _ k _; simp
  | cons b t ih =>
      intro hlen k hk
      have htail : t.length < 63 := by
        simp only [List.length_cons] at hlen
        omega
      have hsum : ((b :: t).map e7BinWeight).sum =
          (t.map e7BinWeight).sum + e7BinWeight b := by
        simp only [List.map_cons, List.sum_cons]
        omega
      have hc : (t.map e7BinWeight).sum / e7CodeBase ^ b % e7CodeBase + 1 < e7CodeBase := by
        have hbase : e7CodeBase = 64 := rfl
        have := e7BinWeight_sum_digit_le t htail b
        omega
      rw [hsum, e7CodeDigit_add_binWeight _ b k hk hc, ih htail k hk, List.count_cons]
      by_cases hbk : b = k
      · rw [if_pos hbk, if_pos (by simp [hbk])]
      · rw [if_neg hbk, if_neg (by simpa using hbk)]

/-! ## The list of minuscule weights -/

/-- The `56` minuscule weight indices, in the order the histogram folds them. -/
def e7WeightList : List E7WeightIndex :=
  [false, true].flatMap fun sign =>
    (List.finRange e7Pairs.length).map fun pair => (sign, pair)

theorem e7WeightList_length : e7WeightList.length = 56 := by decide

theorem e7WeightList_nodup : e7WeightList.Nodup := by decide

theorem e7WeightList_toFinset : e7WeightList.toFinset = Finset.univ := by decide

/-- Bin index of one minuscule weight for a component profile. -/
def e7Bin (profile : Array ℤ) (w : E7WeightIndex) : ℕ :=
  (e7ComponentEvaluation profile w + 21).toNat

/-- The minuscule weights landing in one evaluation bin. -/
def e7BinFinset (profile : Array ℤ) (k : ℕ) : Finset E7WeightIndex :=
  Finset.univ.filter fun w => e7Bin profile w = k

theorem card_e7BinFinset_eq_count (profile : Array ℤ) (k : ℕ) :
    (e7BinFinset profile k).card = (e7WeightList.map (e7Bin profile)).count k := by
  have hcount : (e7WeightList.map (e7Bin profile)).count k =
      (e7WeightList.filter fun w => e7Bin profile w == k).length := by
    rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    rfl
  have hnodup : (e7WeightList.filter fun w => e7Bin profile w == k).Nodup :=
    e7WeightList_nodup.filter _
  rw [hcount, ← List.toFinset_card_of_nodup hnodup, List.toFinset_filter,
    e7WeightList_toFinset]
  congr 1
  ext w
  simp [e7BinFinset]

/-! ## The histogram is the bin count -/

theorem e7ComponentHistogram_eq_binSum (profile : Array ℤ) :
    e7ComponentHistogram profile =
      e7HistogramOfCode ((e7WeightList.map (e7Bin profile)).map e7BinWeight).sum := by
  have hfold : e7ComponentHistogram profile =
      (e7WeightList.map (e7Bin profile)).foldl
        (fun counts i => counts.set! i (counts.getD i 0 + 1)) (e7HistogramOfCode 0) := by
    rw [e7HistogramOfCode_zero]
    simp only [e7ComponentHistogram, e7WeightList, List.foldl_map, e7Bin]
  have hbound : ∀ k : ℕ,
      0 / e7CodeBase ^ k % e7CodeBase + (e7WeightList.map (e7Bin profile)).length <
        e7CodeBase := by
    intro k
    simp only [List.length_map, e7WeightList_length, Nat.zero_div, Nat.zero_mod,
      Nat.zero_add, e7CodeBase]
    decide
  rw [hfold, e7HistogramOfCode_foldl _ 0 hbound, e7BinWeight_foldl, Nat.zero_add]

/-- **Bin `k` of the evaluation histogram counts the minuscule weights whose
evaluation lands in bin `k`.**  The hypothesis is that no evaluation escapes the
`43` bins; outside the bin range both sides vanish. -/
theorem e7ComponentHistogram_getD (profile : Array ℤ)
    (hrange : ∀ w, e7Bin profile w < 43) (k : ℕ) :
    (e7ComponentHistogram profile).getD k 0 = (e7BinFinset profile k).card := by
  rw [e7ComponentHistogram_eq_binSum profile, e7HistogramOfCode_getD_eq, e7CodeDigit,
    card_e7BinFinset_eq_count]
  by_cases hk : k < 43
  · rw [if_pos hk]
    exact e7BinWeight_sum_digit _ (by simp [e7WeightList_length]) k hk
  · rw [if_neg hk]
    symm
    rw [List.count_eq_zero]
    intro hmem
    obtain ⟨w, -, hw⟩ := List.mem_map.mp hmem
    exact hk (hw ▸ hrange w)

/-! ## The convolution counts eligible pairs -/

variable {y₁ y₂ : Fin 8 → ℤ}

/-- The eligible pairs with a prescribed left bin are a product of two bins. -/
theorem filter_eligible_bin_eq_product (p₁ p₂ : Array ℤ)
    (heq : ∀ w : E7ShellIndex,
      e7Eligible y₁ y₂ w ↔ e7Bin p₁ w.1 + e7Bin p₂ w.2 = 57)
    (k : ℕ) (hk : k < 43) :
    (Finset.univ.filter fun w : E7ShellIndex =>
        e7Eligible y₁ y₂ w ∧ e7Bin p₁ w.1 = k) =
      (e7BinFinset p₁ k) ×ˢ (e7BinFinset p₂ (57 - k)) := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
    e7BinFinset, heq w]
  omega

/-- Eligible pairs with a prescribed left bin, counted. -/
theorem card_filter_eligible_bin (p₁ p₂ : Array ℤ)
    (heq : ∀ w : E7ShellIndex,
      e7Eligible y₁ y₂ w ↔ e7Bin p₁ w.1 + e7Bin p₂ w.2 = 57)
    (k : ℕ) (hk : k < 43) :
    (Finset.univ.filter fun w : E7ShellIndex =>
        e7Eligible y₁ y₂ w ∧ e7Bin p₁ w.1 = k).card =
      (e7BinFinset p₁ k).card * (e7BinFinset p₂ (57 - k)).card := by
  rw [filter_eligible_bin_eq_product p₁ p₂ heq k hk, Finset.card_product]

/-- **The eligible pairs of one left bin, inside the eligible index type.**
This is the capacity of the `k`-th scalar dynamic-programming category. -/
theorem card_e7EligibleIndex_bin_fiber (p₁ p₂ : Array ℤ)
    (heq : ∀ w : E7ShellIndex,
      e7Eligible y₁ y₂ w ↔ e7Bin p₁ w.1 + e7Bin p₂ w.2 = 57)
    (k : ℕ) (hk : k < 43) :
    (Finset.univ.filter fun u : E7EligibleIndex y₁ y₂ => e7Bin p₁ u.1.1 = k).card =
      (e7BinFinset p₁ k).card * (e7BinFinset p₂ (57 - k)).card := by
  classical
  have h1 : (Finset.univ.filter fun u : E7EligibleIndex y₁ y₂ => e7Bin p₁ u.1.1 = k).card =
      Fintype.card {u : E7EligibleIndex y₁ y₂ // e7Bin p₁ u.1.1 = k} :=
    (Fintype.card_subtype _).symm
  have h2 : Fintype.card {u : E7EligibleIndex y₁ y₂ // e7Bin p₁ u.1.1 = k} =
      Fintype.card {w : E7ShellIndex // e7Eligible y₁ y₂ w ∧ e7Bin p₁ w.1 = k} :=
    Fintype.card_congr
      (Equiv.subtypeSubtypeEquivSubtypeInter (e7Eligible y₁ y₂)
        fun w : E7ShellIndex => e7Bin p₁ w.1 = k)
  have h3 : Fintype.card {w : E7ShellIndex // e7Eligible y₁ y₂ w ∧ e7Bin p₁ w.1 = k} =
      (Finset.univ.filter fun w : E7ShellIndex =>
        e7Eligible y₁ y₂ w ∧ e7Bin p₁ w.1 = k).card :=
    Fintype.card_subtype _
  rw [h1, h2, h3, card_filter_eligible_bin p₁ p₂ heq k hk]

private theorem foldl_range_add (f : ℕ → ℕ) :
    ∀ (n c : ℕ), (List.range n).foldl (fun total k => total + f k) c =
      c + ∑ k ∈ Finset.range n, f k := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
      intro c
      rw [List.range_succ, List.foldl_append, ih c, Finset.sum_range_succ]
      simp only [List.foldl_cons, List.foldl_nil]
      omega

/-- **The histogram convolution is the number of eligible paired weights.**
Bin `k` on the left meets bin `57 - k` on the right exactly when the two
minuscule evaluations sum to `15`, which is `SRG266.e7Eligible`. -/
theorem card_e7EligibleIndex_eq_histogramEligibleCount (p₁ p₂ : Array ℤ)
    (hrange₁ : ∀ w, e7Bin p₁ w < 43) (hrange₂ : ∀ w, e7Bin p₂ w < 43)
    (heq : ∀ w : E7ShellIndex,
      e7Eligible y₁ y₂ w ↔ e7Bin p₁ w.1 + e7Bin p₂ w.2 = 57) :
    Fintype.card (E7EligibleIndex y₁ y₂) =
      e7HistogramEligibleCount (e7ComponentKey p₁) (e7ComponentKey p₂) := by
  classical
  have hfiber :
      (Finset.univ.filter (e7Eligible y₁ y₂)).card =
        ∑ k ∈ Finset.range 43,
          (Finset.univ.filter fun w : E7ShellIndex =>
            e7Eligible y₁ y₂ w ∧ e7Bin p₁ w.1 = k).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun w : E7ShellIndex => e7Bin p₁ w.1) (t := Finset.range 43)
      (fun w _ => Finset.mem_range.mpr (hrange₁ w.1))]
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.filter_filter]
  rw [Fintype.card_subtype, hfiber, e7HistogramEligibleCount, foldl_range_add,
    Nat.zero_add]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [card_filter_eligible_bin p₁ p₂ heq k (Finset.mem_range.mp hk),
    e7ComponentKey, e7ComponentKey, e7ComponentHistogram_getD p₁ hrange₁,
    e7ComponentHistogram_getD p₂ hrange₂]

end Lattice
end SRG266
