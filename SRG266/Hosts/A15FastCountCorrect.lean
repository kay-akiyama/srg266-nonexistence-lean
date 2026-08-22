/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15PairHistogram
import SRG266.Hosts.A15QuadReindex

/-!
# The fast and reference A15 eligible-shell counters agree at the threshold

The magnitude enumerator only ever asks whether a reduced norm profile carries
at least seventy-four eligible shell vectors.  Two counters answer that
question:

* `a15ExactEligibleCardReduced` folds the eligibility predicate over the
  checked 1,820-entry four-subset table;
* `a15FastEligibleCountReduced` runs a byte pair-sum histogram and stops as
  soon as the running total reaches seventy-four.

The two are not equal as numbers -- the fast loop caps -- but they agree on
the predicate `74 ≤ ·`, which is all the enumerator uses.  This module proves
that agreement for the two residues the search runs at.

The argument is a double count.  Both counters range over the quadruples
`i < j < k < l < 16` whose shifted coordinate sum hits a target base.  The
fast loop visits them in the order `(k, l, j, i)`: at stage `k` its histogram
holds every pair `i < j < k`, and pairing those with the completions
`k < l < 16` meets each quadruple exactly once, at `k` its third element.
`a15SliceCount` names one such stage.  Reindexing the table through
`a15QuadsByThird` produces the same slices, and the capped accumulator
crosses seventy-four exactly when the uncapped sum of the slices does.

Nothing here is evaluated: unfolding the reference fold over the table
literal is far beyond the kernel's budget, so every step is a rewrite.
-/

open scoped BigOperators

namespace SRG266

set_option maxRecDepth 10000

/-- The four-subsets whose third element is `k`, counted by target sum. -/
def a15SliceCount (S : ℕ → ℕ) (tb k : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (15 - k),
    ∑ j ∈ Finset.range k,
      (List.range j).countP (fun i => S i + S j + S k + S (k + 1 + t) == tb)

/-- Unfolding the outer loop below the early-exit threshold. -/
theorem a15FastFourSumCountLoop_succ (bs : ByteArray) (tb1 tb2 k fuel : ℕ)
    (counts : ByteArray) (total : ℕ) (htot : ¬ 74 ≤ total) :
    a15FastFourSumCountLoop bs tb1 tb2 k (fuel + 1) counts total =
      a15FastFourSumCountLoop bs tb1 tb2 (k + 1) fuel
        (a15AddPairSums bs (k - 1) (k - 1) counts)
        (total +
            a15CountPairCompletions bs
              (a15AddPairSums bs (k - 1) (k - 1) counts) tb1 k (k + 1)
              (15 - k) +
            a15CountPairCompletions bs
              (a15AddPairSums bs (k - 1) (k - 1) counts) tb2 k (k + 1)
              (15 - k)) := by
  rw [a15FastFourSumCountLoop, if_neg htot]

/-- Unfolding the outer loop at or above the early-exit threshold. -/
theorem a15FastFourSumCountLoop_cap (bs : ByteArray) (tb1 tb2 k fuel : ℕ)
    (counts : ByteArray) (total : ℕ) (htot : 74 ≤ total) :
    a15FastFourSumCountLoop bs tb1 tb2 k (fuel + 1) counts total = total := by
  rw [a15FastFourSumCountLoop, if_pos htot]

section

variable (bs : ByteArray) (S : ℕ → ℕ)

/-- One completion pass reproduces the slice count.  Where the byte-range
guard fails, the true count is zero: the pair sums stored in the histogram
lie in `[0,68]`, so an unrepresentable complement cannot occur. -/
theorem a15CountPairCompletions_eq_slice
    (hS : ∀ i, S i = (bs.get! i).toNat)
    (hbound : ∀ i, i < 16 → S i ≤ 34)
    (tb k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 14) (counts : ByteArray)
    (hcounts : ∀ s, (counts.get! s).toNat = a15PairSumCount S k s) :
    a15CountPairCompletions bs counts tb k (k + 1) (15 - k) =
      a15SliceCount S tb k := by
  rw [a15CountPairCompletions_eq]
  simp only [← hS]
  unfold a15SliceCount
  refine Finset.sum_congr rfl ?_
  intro t ht
  have htlt : t < 15 - k := Finset.mem_range.mp ht
  have hl : k + 1 + t < 16 := by omega
  have hklt : k < 16 := by omega
  have hSk : S k ≤ 34 := hbound k hklt
  have hSl : S (k + 1 + t) ≤ 34 := hbound _ hl
  by_cases hguard : S k + S (k + 1 + t) ≤ tb ∧ tb - (S k + S (k + 1 + t)) ≤ 68
  · rw [if_pos hguard, hcounts]
    unfold a15PairSumCount
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    refine List.countP_congr ?_
    intro i _
    simp only [beq_iff_eq]
    omega
  · rw [if_neg hguard]
    symm
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hSj : S j ≤ 34 := hbound j (by omega)
    refine List.countP_eq_zero.mpr ?_
    intro i hi
    have hij : i < j := List.mem_range.mp hi
    have hSi : S i ≤ 34 := hbound i (by omega)
    simp only [beq_iff_eq]
    omega

/-- The early-exiting outer loop agrees with its abstract model.  The
invariant entering stage `k` is that the histogram holds every pair
`i < j < k - 1 + 1`; the byte cells cannot overflow because at most `13 * 13`
pairs are ever recorded in one cell. -/
theorem a15FastFourSumCountLoop_eq_mock
    (hS : ∀ i, S i = (bs.get! i).toNat)
    (hbound : ∀ i, i < 16 → S i ≤ 34) (tb1 tb2 : ℕ) :
    ∀ (fuel k : ℕ) (counts : ByteArray) (total : ℕ),
      2 ≤ k → k + fuel ≤ 15 → counts.size = 69 →
      (∀ s, (counts.get! s).toNat = a15PairSumCount S (k - 1) s) →
      a15FastFourSumCountLoop bs tb1 tb2 k fuel counts total =
        a15MockLoop
          (fun k => a15SliceCount S tb1 k + a15SliceCount S tb2 k)
          k fuel total := by
  intro fuel
  induction fuel with
  | zero =>
      intro k counts total _ _ _ _
      simp [a15FastFourSumCountLoop, a15MockLoop]
  | succ fuel ih =>
      intro k counts total hk hkf hsize hcounts
      by_cases htot : 74 ≤ total
      · rw [a15FastFourSumCountLoop_cap _ _ _ _ _ _ _ htot, a15MockLoop,
          if_pos htot]
      rw [a15FastFourSumCountLoop_succ _ _ _ _ _ _ _ htot, a15MockLoop,
        if_neg htot]
      have hsize' : (a15AddPairSums bs (k - 1) (k - 1) counts).size = 69 := by
        rw [a15AddPairSums_size, hsize]
      have hstep : ∀ s,
          ((a15AddPairSums bs (k - 1) (k - 1) counts).get! s).toNat =
            a15PairSumCount S k s := by
        intro s
        have hidx : ∀ i, i < k - 1 →
            (bs.get! i).toNat + (bs.get! (k - 1)).toNat < 69 := by
          intro i hi
          have h1 : S i ≤ 34 := hbound i (by omega)
          have h2 : S (k - 1) ≤ 34 := hbound (k - 1) (by omega)
          rw [← hS, ← hS]
          omega
        have hsmall : ∀ t, (counts.get! t).toNat + (k - 1) < 256 := by
          intro t
          have h1 := hcounts t
          have h2 := a15PairSumCount_le S (k - 1) t
          have h3 : (k - 1) * (k - 1) ≤ 169 := by
            have hle : k - 1 ≤ 13 := by omega
            calc (k - 1) * (k - 1) ≤ 13 * 13 := Nat.mul_le_mul hle hle
              _ = 169 := by norm_num
          omega
        have hsucc := a15PairSumCount_succ S (k - 1) s
        rw [show k - 1 + 1 = k by omega] at hsucc
        rw [a15AddPairSums_get bs (k - 1) (k - 1) counts s hsize hidx hsmall,
          hcounts s, hsucc]
        simp only [← hS]
      have hcomp1 :
          a15CountPairCompletions bs (a15AddPairSums bs (k - 1) (k - 1) counts)
              tb1 k (k + 1) (15 - k) = a15SliceCount S tb1 k :=
        a15CountPairCompletions_eq_slice bs S hS hbound tb1 k hk (by omega) _
          hstep
      have hcomp2 :
          a15CountPairCompletions bs (a15AddPairSums bs (k - 1) (k - 1) counts)
              tb2 k (k + 1) (15 - k) = a15SliceCount S tb2 k :=
        a15CountPairCompletions_eq_slice bs S hS hbound tb2 k hk (by omega) _
          hstep
      have hnext : ∀ s,
          ((a15AddPairSums bs (k - 1) (k - 1) counts).get! s).toNat =
            a15PairSumCount S (k + 1 - 1) s := fun s => hstep s
      rw [hcomp1, hcomp2, Nat.add_assoc]
      exact ih (k + 1) _ _ (by omega) (by omega) hsize' hnext

end

/-! ### Reindexing the reference count -/

theorem a15_countP_flatMap {α β : Type*} (l : List α) (f : α → List β)
    (p : β → Bool) :
    (l.flatMap f).countP p = (l.map (fun x => (f x).countP p)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.countP_append, ih]

theorem a15_sum_map_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih,
        Finset.sum_range_succ]
      simp

theorem a15_sum_map_range' (n : ℕ) (f : ℕ → ℕ) :
    ∀ a : ℕ,
      ((List.range' a n).map f).sum = ∑ i ∈ Finset.range n, f (a + i) := by
  induction n with
  | zero => intro a; simp
  | succ n ih =>
      intro a
      rw [List.range'_succ, List.map_cons, List.sum_cons, ih (a + 1),
        a15_sum_range_shift_succ f a n]

/-- The `k`-slice of the reindexed quadruple list counts exactly the
four-subsets whose third element is `k`. -/
theorem a15_slice_countP (S : ℕ → ℕ) (tb k : ℕ) :
    (((List.range' (k + 1) (15 - k)).flatMap fun l =>
        (List.range k).flatMap fun j =>
          (List.range j).map fun i => (i, j, k, l))).countP
        (fun q => S q.1 + S q.2.1 + S q.2.2.1 + S q.2.2.2 == tb) =
      a15SliceCount S tb k := by
  rw [a15_countP_flatMap, a15_sum_map_range']
  unfold a15SliceCount
  refine Finset.sum_congr rfl ?_
  intro t _
  rw [a15_countP_flatMap, a15_sum_map_range]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [List.countP_map]
  rfl

/-- The whole reindexed quadruple list splits into the slices. -/
theorem a15_quadsByThird_countP (S : ℕ → ℕ) (tb : ℕ) :
    a15QuadsByThird.countP
        (fun q => S q.1 + S q.2.1 + S q.2.2.1 + S q.2.2.2 == tb) =
      ∑ i ∈ Finset.range 13, a15SliceCount S tb (2 + i) := by
  unfold a15QuadsByThird
  rw [a15_countP_flatMap, a15_sum_map_range']
  exact Finset.sum_congr rfl fun i _ => a15_slice_countP S tb (2 + i)

/-! ### The two counters agree at the threshold -/

theorem a15FastEligibleCountReduced_eq (residue : ℤ) (coordinates : List ℤ) :
    a15FastEligibleCountReduced residue coordinates =
      a15FastFourSumCountLoop (a15ShiftedReducedCoordinateBytes coordinates)
        (if residue = 0 then 83 else 81) (if residue = 0 then 53 else 51)
        2 13 ⟨Array.replicate 69 0⟩ 0 := rfl

theorem a15ReducedDataEligible_eq (residue : ℤ) (coordinates : List ℤ)
    (s : A15FourSubset) :
    a15ReducedDataEligible residue coordinates s =
      (decide (a15ReducedDataSubsetSum coordinates s = 15 - residue) ||
        decide (a15ReducedDataSubsetSum coordinates s = -15 - residue)) := rfl

/-- The reference count for one target sum, reindexed into the slices the
fast loop accumulates.  The shift by `68` is the four coordinate shifts by
`17` carried by the byte encoding. -/
theorem a15_exact_count_eq_slices (coordinates : List ℤ)
    (T : ℤ) (tb : ℕ) (htb : (tb : ℤ) = T + 68) (S : ℕ → ℕ)
    (hSval : ∀ i, i < 16 → (S i : ℤ) = coordinates.getD i 0 + 17) :
    a15FourSubsetData.toList.countP
        (fun s => decide (a15ReducedDataSubsetSum coordinates s = T)) =
      ∑ i ∈ Finset.range 13, a15SliceCount S tb (2 + i) := by
  have h1 : a15FourSubsetData.toList.countP
      (fun s => decide (a15ReducedDataSubsetSum coordinates s = T)) =
      a15TableQuads.countP (fun q =>
        decide (coordinates.getD q.1 0 + coordinates.getD q.2.1 0 +
          coordinates.getD q.2.2.1 0 + coordinates.getD q.2.2.2 0 = T)) := by
    rw [a15TableQuads, List.countP_map]
    rfl
  rw [h1, a15TableQuads_perm.countP_eq]
  rw [show a15QuadsByThird.countP (fun q =>
        decide (coordinates.getD q.1 0 + coordinates.getD q.2.1 0 +
          coordinates.getD q.2.2.1 0 + coordinates.getD q.2.2.2 0 = T)) =
      a15QuadsByThird.countP
        (fun q => S q.1 + S q.2.1 + S q.2.2.1 + S q.2.2.2 == tb) from ?_]
  · exact a15_quadsByThird_countP S tb
  refine List.countP_congr ?_
  intro q hq
  obtain ⟨i, j, k, l⟩ := q
  have hq' : i < j ∧ j < k ∧ k < l ∧ l < 16 :=
    (a15_mem_quadsByThird (i, j, k, l)).mp hq
  obtain ⟨hij, hjk, hkl, hl⟩ := hq'
  have hi := hSval i (by omega)
  have hj := hSval j (by omega)
  have hk := hSval k (by omega)
  have hll := hSval l (by omega)
  simp only [decide_eq_true_eq, beq_iff_eq]
  omega

/-- The reference and fast eligible-shell counters answer the enumerator's
threshold question identically on every bounded reduced norm profile, for the
two residues the A15 search runs at. -/
theorem a15_counters_agree (residue : ℤ) (hres : residue = 0 ∨ residue = 2)
    (coordinates : List ℤ) (hlen : coordinates.length = 16)
    (hb : ∀ z ∈ coordinates, -17 ≤ z ∧ z ≤ 17) :
    (74 ≤ a15ExactEligibleCardReduced residue coordinates ↔
      74 ≤ a15FastEligibleCountReduced residue coordinates) := by
  set bs := a15ShiftedReducedCoordinateBytes coordinates with hbs
  set S : ℕ → ℕ := fun i => (bs.get! i).toNat with hSdef
  have hS : ∀ i, S i = (bs.get! i).toNat := fun _ => rfl
  have hcb : ∀ i, i < 16 →
      -17 ≤ coordinates.getD i 0 ∧ coordinates.getD i 0 ≤ 17 := by
    intro i hi
    rw [List.getD_eq_getElem coordinates 0 (by omega)]
    exact hb _ (List.getElem_mem _)
  have hSval : ∀ i, i < 16 → (S i : ℤ) = coordinates.getD i 0 + 17 := by
    intro i hi
    rw [hS, hbs,
      a15ShiftedReducedCoordinateBytes_get coordinates i (by omega) hb]
    have := hcb i hi
    omega
  have hbound : ∀ i, i < 16 → S i ≤ 34 := by
    intro i hi
    have h1 := hSval i hi
    have h2 := hcb i hi
    omega
  set tb1 : ℕ := if residue = 0 then 83 else 81 with htb1
  set tb2 : ℕ := if residue = 0 then 53 else 51 with htb2
  have hfast : a15FastEligibleCountReduced residue coordinates =
      a15MockLoop (fun k => a15SliceCount S tb1 k + a15SliceCount S tb2 k)
        2 13 0 := by
    rw [a15FastEligibleCountReduced_eq, ← hbs, ← htb1, ← htb2]
    refine a15FastFourSumCountLoop_eq_mock bs S hS hbound tb1 tb2 13 2
      ⟨Array.replicate 69 0⟩ 0 (by omega) (by omega) ?_ ?_
    · simp [ByteArray.size]
    · intro s
      simp [a15ByteArray_get!_replicate, a15PairSumCount]
  have hexact : a15ExactEligibleCardReduced residue coordinates =
      ∑ i ∈ Finset.range 13,
        (a15SliceCount S tb1 (2 + i) + a15SliceCount S tb2 (2 + i)) := by
    rw [a15ExactEligibleCardReduced_eq_countP]
    have hdisj : ∀ s ∈ a15FourSubsetData.toList,
        ¬ (decide (a15ReducedDataSubsetSum coordinates s = 15 - residue)
              = true ∧
            decide (a15ReducedDataSubsetSum coordinates s = -15 - residue)
              = true) := by
      intro s _
      simp only [decide_eq_true_eq, not_and]
      intro h1 h2
      omega
    have hsplit : a15FourSubsetData.toList.countP
        (fun s => a15ReducedDataEligible residue coordinates s) =
        a15FourSubsetData.toList.countP
          (fun s =>
            decide (a15ReducedDataSubsetSum coordinates s = 15 - residue)) +
        a15FourSubsetData.toList.countP
          (fun s =>
            decide (a15ReducedDataSubsetSum coordinates s = -15 - residue)) := by
      rw [← a15_countP_or_disjoint _ _ _ hdisj]
      exact List.countP_congr fun s _ => by rw [a15ReducedDataEligible_eq]
    rw [hsplit,
      a15_exact_count_eq_slices coordinates (15 - residue) tb1
        (by rcases hres with h | h <;> simp [h, htb1]) S hSval,
      a15_exact_count_eq_slices coordinates (-15 - residue) tb2
        (by rcases hres with h | h <;> simp [h, htb2]) S hSval,
      ← Finset.sum_add_distrib]
  rw [hexact, hfast, a15MockLoop_threshold, a15_sum_map_range]
  simp

end SRG266
