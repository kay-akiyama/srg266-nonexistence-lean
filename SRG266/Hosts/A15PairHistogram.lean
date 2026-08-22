/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15ShiftedBytes

/-!
# The pair-sum histogram of the fast A15 counter

The fast eligible-shell counter keeps a byte histogram of the shifted pair
sums `(a_i + 17) + (a_j + 17)` for the already processed indices `i < j`.
This module establishes the three local facts the outer loop needs.

* `a15PairSumCount` is the declarative content of the histogram, and
  `a15AddPairSums_get` shows the imperative update realizes it.  The byte
  cells never overflow because the histogram only ever holds pairs drawn from
  the fourteen indices `0, …, 13`.
* `a15CountPairCompletions_eq` turns the completion loop into a finite sum
  over the completions `l`.
* `a15MockLoop` abstracts the early-exiting accumulation of the outer loop:
  the capped accumulator reaches the threshold `74` exactly when the uncapped
  total does.
-/

open scoped BigOperators

namespace SRG266

set_option maxRecDepth 10000

/-- Declarative content of the pair histogram: the number of pairs
`i < j < k` whose shifted sum is `s`. -/
def a15PairSumCount (S : ℕ → ℕ) (k s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, ((List.range j).countP (fun i => S i + S j == s))

theorem a15PairSumCount_zero (S : ℕ → ℕ) (s : ℕ) :
    a15PairSumCount S 0 s = 0 := by
  simp [a15PairSumCount]

theorem a15PairSumCount_succ (S : ℕ → ℕ) (k s : ℕ) :
    a15PairSumCount S (k + 1) s =
      a15PairSumCount S k s +
        (List.range k).countP (fun i => S i + S k == s) := by
  simp [a15PairSumCount, Finset.sum_range_succ]

/-- Every histogram cell counts pairs drawn from `k` indices, hence stays
well below the byte range for the fourteen indices used here. -/
theorem a15PairSumCount_le (S : ℕ → ℕ) (k s : ℕ) :
    a15PairSumCount S k s ≤ k * k := by
  have h : ∀ j ∈ Finset.range k,
      (List.range j).countP (fun i => S i + S j == s) ≤ k := by
    intro j hj
    have h1 : (List.range j).countP (fun i => S i + S j == s) ≤
        (List.range j).length := List.countP_le_length
    have h2 : j < k := Finset.mem_range.mp hj
    simp only [List.length_range] at h1
    omega
  calc a15PairSumCount S k s ≤ ∑ _j ∈ Finset.range k, k :=
        Finset.sum_le_sum h
    _ = k * k := by simp

/-- `a15AddPairSums` preserves the histogram length. -/
theorem a15AddPairSums_size (bs : ByteArray) (j : ℕ) :
    ∀ (n : ℕ) (counts : ByteArray),
      (a15AddPairSums bs j n counts).size = counts.size := by
  intro n
  induction n with
  | zero => intro counts; simp [a15AddPairSums]
  | succ n ih =>
      intro counts
      rw [a15AddPairSums, ih]
      exact a15ByteArray_size_set! _ _ _

/-- `a15AddPairSums bs j n` adds the pairs `(i, j)` for `i < n` to the
histogram.  The hypotheses record that all inserted indices are in range and
that no byte cell overflows. -/
theorem a15AddPairSums_get (bs : ByteArray) (j : ℕ) :
    ∀ (n : ℕ) (counts : ByteArray) (s : ℕ),
      counts.size = 69 →
      (∀ i < n, (bs.get! i).toNat + (bs.get! j).toNat < 69) →
      (∀ t, (counts.get! t).toNat + n < 256) →
      ((a15AddPairSums bs j n counts).get! s).toNat =
        (counts.get! s).toNat +
          ((List.range n).countP
            (fun i => (bs.get! i).toNat + (bs.get! j).toNat == s)) := by
  intro n
  induction n with
  | zero => intro counts s _ _ _; simp [a15AddPairSums]
  | succ n ih =>
      intro counts s hsize hidx hsmall
      set index := (bs.get! n).toNat + (bs.get! j).toNat with hindexDef
      have hindexLt : index < 69 := hidx n (by omega)
      set counts' :=
        counts.set! index ((counts.get! index).toNat + 1).toUInt8 with hcounts'
      have hsize' : counts'.size = 69 := by
        rw [hcounts', a15ByteArray_size_set!, hsize]
      have hval : ∀ t, (counts'.get! t).toNat =
          (counts.get! t).toNat + (if index = t then 1 else 0) := by
        intro t
        by_cases h : index = t
        · subst h
          rw [hcounts',
            a15ByteArray_get!_set!_self _ _ _ (by rw [hsize]; omega)]
          have hlt : (counts.get! index).toNat + 1 < 256 := by
            have := hsmall index; omega
          simp only [Nat.toUInt8, UInt8.toNat_ofNat', Nat.reducePow]
          rw [Nat.mod_eq_of_lt hlt]
          simp
        · rw [hcounts', a15ByteArray_get!_set!_ne _ _ _ _ h]
          simp [h]
      have hsmall' : ∀ t, (counts'.get! t).toNat + n < 256 := by
        intro t
        rw [hval t]
        have := hsmall t
        split <;> omega
      rw [a15AddPairSums, ← hcounts']
      rw [ih counts' s hsize' (fun i hi => hidx i (by omega)) hsmall']
      rw [hval s]
      rw [List.range_succ, List.countP_append]
      simp only [List.countP_cons, List.countP_nil, Nat.zero_add, beq_iff_eq,
        ← hindexDef]
      omega

/-- Peel the first summand of a shifted range sum. -/
theorem a15_sum_range_shift_succ (F : ℕ → ℕ) (l n : ℕ) :
    (∑ t ∈ Finset.range (n + 1), F (l + t)) =
      F l + ∑ t ∈ Finset.range n, F (l + 1 + t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hidx : l + (n + 1) = l + 1 + n := by omega
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Nat.add_assoc,
        hidx]

/-- Closed form of the completion loop as a finite sum over `l`. -/
theorem a15CountPairCompletions_eq (bs counts : ByteArray) (targetBase k : ℕ) :
    ∀ (fuel l : ℕ),
      a15CountPairCompletions bs counts targetBase k l fuel =
        ∑ t ∈ Finset.range fuel,
          (if (bs.get! k).toNat + (bs.get! (l + t)).toNat ≤ targetBase ∧
                targetBase - ((bs.get! k).toNat + (bs.get! (l + t)).toNat)
                  ≤ 68 then
              (counts.get!
                (targetBase -
                  ((bs.get! k).toNat + (bs.get! (l + t)).toNat))).toNat
            else 0) := by
  intro fuel
  induction fuel with
  | zero => intro l; simp [a15CountPairCompletions]
  | succ fuel ih =>
      intro l
      rw [a15CountPairCompletions, ih (l + 1),
        a15_sum_range_shift_succ (fun x =>
          if (bs.get! k).toNat + (bs.get! x).toNat ≤ targetBase ∧
              targetBase - ((bs.get! k).toNat + (bs.get! x).toNat) ≤ 68 then
            (counts.get!
              (targetBase - ((bs.get! k).toNat + (bs.get! x).toNat))).toNat
          else 0) l fuel]

/-- Abstract model of the early-exiting accumulation loop. -/
def a15MockLoop (step : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, total => total
  | k, fuel + 1, total =>
      if 74 ≤ total then total
      else a15MockLoop step (k + 1) fuel (total + step k)

/-- The capped accumulator crosses the threshold exactly when the uncapped
total does. -/
theorem a15MockLoop_threshold (step : ℕ → ℕ) :
    ∀ (fuel k total : ℕ),
      (74 ≤ a15MockLoop step k fuel total ↔
        74 ≤ total + ((List.range fuel).map (fun i => step (k + i))).sum) := by
  intro fuel
  induction fuel with
  | zero => intro k total; simp [a15MockLoop]
  | succ fuel ih =>
      intro k total
      rw [a15MockLoop]
      by_cases h : 74 ≤ total
      · rw [if_pos h]
        constructor
        · intro _; omega
        · intro _; exact h
      · rw [if_neg h, ih (k + 1) (total + step k), List.range_succ_eq_map]
        simp only [List.map_cons, List.sum_cons, List.map_map,
          Function.comp_def, Nat.add_zero, Nat.succ_eq_add_one]
        have hcongr :
            ((List.range fuel).map (fun i => step (k + 1 + i))).sum =
              ((List.range fuel).map (fun i => step (k + (i + 1)))).sum := by
          congr 1
          apply List.map_congr_left
          intro i _
          congr 1
          omega
        rw [hcongr]
        omega

end SRG266
