/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15PackedDigits
import SRG266.Hosts.A15FastCountCorrect

/-!
# A generating-function eligible-shell counter for the A15 search

The A15 magnitude search asks one question at each of its 420,403 terminal
norm profiles: does the profile carry at least seventy-four eligible shell
vectors, that is, do at least seventy-four of the 1,820 index quadruples
`i < j < k < l < 16` have reduced coordinate sum `15 - r` or `-15 - r`?

`a15FastEligibleCountReduced` answers it with a byte pair-sum histogram, but
each `ByteArray.set!` rebuilds a sixty-nine element list in kernel reduction.

This module answers the same question with one big natural number.  Write
`b i = a i + 17 ∈ [0,34]` for the shifted coordinates and consider

  `∏ i < 16, (1 + y * x ^ b i)`,

whose `y^4 x^t` coefficient is the number of four-subsets of shifted sum `t`.
Packing the pair `(u, t)` of `y`- and `x`-degrees into the single index
`576 * u + t` -- legitimate because `t ≤ 34 * 16 = 544 < 576` -- and storing
each coefficient in one base-`2 ^ 32` digit turns the product into sixteen
steps `p ↦ p + p <<< (32 * (576 + b i))` of GMP-accelerated arithmetic.

The correctness proof is a five-rung ladder.  `a15PolyCoeff` is the digit
function of the product, `a15Q0 … a15Q4` are the numbers of index subsets of
size zero to four with a prescribed shifted sum, and rung `u` identifies the
digits in slot `u` with `a15Qu`.  Slot four is then matched with
`a15SliceCount`, the decomposition through which
`A15FastCountCorrect` already routes the byte histogram, so both counters end
up compared with the checked 1,820-entry four-subset table.
-/

open scoped BigOperators

namespace SRG266

set_option maxRecDepth 8000

/-- Stride between consecutive subset-size slots.  Any value above
`34 * 16 = 544`, the largest possible shifted subset sum, keeps the slots
disjoint. -/
def a15PolySlot : ℕ := 576

/-- The shifted coordinate at position `i`, in `[0,34]` for a reduced
profile. -/
def a15ShiftedCoord (coordinates : List ℤ) (i : ℕ) : ℕ :=
  (coordinates.getD i 0 + 17).toNat

/-- One factor `1 + y * x ^ b` of the generating function. -/
def a15PolyStep (b p : ℕ) : ℕ := p + p <<< (32 * (a15PolySlot + b))

/-- Generating function of the first `n` shifted coordinates. -/
def a15PolyProd (S : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => a15PolyStep (S n) (a15PolyProd S n)

/-- Digit function of `a15PolyProd`. -/
def a15PolyCoeff (S : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => fun s => if s = 0 then 1 else 0
  | n + 1 => fun s =>
      a15PolyCoeff S n s +
        (if a15PolySlot + S n ≤ s then
            a15PolyCoeff S n (s - (a15PolySlot + S n))
          else 0)

/-- Number of digits carried by the packed product. -/
def a15PolyLength : ℕ := 9792

theorem a15PolyCoeff_succ (S : ℕ → ℕ) (n s : ℕ) :
    a15PolyCoeff S (n + 1) s =
      a15PolyCoeff S n s +
        (if a15PolySlot + S n ≤ s then
            a15PolyCoeff S n (s - (a15PolySlot + S n))
          else 0) := rfl

/-- Every coefficient counts subsets of an `n`-element index set. -/
theorem a15PolyCoeff_le (S : ℕ → ℕ) : ∀ (n s : ℕ), a15PolyCoeff S n s ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => intro s; unfold a15PolyCoeff; split <;> simp
  | succ n ih =>
      intro s
      rw [a15PolyCoeff_succ, pow_succ]
      have h1 := ih s
      have h2 := ih (s - (a15PolySlot + S n))
      split <;> omega

theorem a15PolyCoeff_lt_base (S : ℕ → ℕ) (n s : ℕ) (hn : n ≤ 16) :
    a15PolyCoeff S n s < a15DigitBase := by
  have h1 := a15PolyCoeff_le S n s
  have h2 : (2 : ℕ) ^ n ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) hn
  simp only [a15DigitBase]
  omega

/-- Coefficients vanish above the largest reachable packed index. -/
theorem a15PolyCoeff_eq_zero (S : ℕ → ℕ) (hS : ∀ i, S i ≤ 34) :
    ∀ (n s : ℕ), n * 610 < s → a15PolyCoeff S n s = 0 := by
  intro n
  induction n with
  | zero => intro s hs; unfold a15PolyCoeff; rw [if_neg (by omega)]
  | succ n ih =>
      intro s hs
      have hSn := hS n
      rw [a15PolyCoeff_succ, ih s (by omega)]
      by_cases hguard : a15PolySlot + S n ≤ s
      · rw [if_pos hguard, ih _ (by simp only [a15PolySlot] at hguard ⊢; omega)]
      · rw [if_neg hguard]

/-- The generating function is the packed coefficient function. -/
theorem a15PolyProd_eq_pack (S : ℕ → ℕ) (hS : ∀ i, S i ≤ 34) :
    ∀ n : ℕ, n ≤ 16 →
      a15PolyProd S n = a15Pack (a15PolyCoeff S n) a15PolyLength := by
  have hslot : a15PolySlot = 576 := rfl
  have hlen : a15PolyLength = 9792 := rfl
  intro n
  induction n with
  | zero =>
      intro _
      rw [a15PolyProd, show a15PolyCoeff S 0 = fun s => if s = 0 then 1 else 0 from rfl,
        a15Pack_delta a15PolyLength (by omega)]
  | succ n ih =>
      intro hn
      have hSn := hS n
      set d : ℕ := a15PolySlot + S n with hd
      have hzero : ∀ v, a15PolyLength ≤ v + d → a15PolyCoeff S n v = 0 := by
        intro v hv
        exact a15PolyCoeff_eq_zero S hS n v (by omega)
      have hshifted : ∀ v, a15PolyLength ≤ v →
          (if d ≤ v then a15PolyCoeff S n (v - d) else 0) = 0 := by
        intro v hv
        by_cases hle : d ≤ v
        · rw [if_pos hle]
          exact hzero _ (by omega)
        · rw [if_neg hle]
      have hcut :
          a15Pack (fun v => if d ≤ v then a15PolyCoeff S n (v - d) else 0)
              (a15PolyLength + d) =
            a15Pack (fun v => if d ≤ v then a15PolyCoeff S n (v - d) else 0)
              a15PolyLength :=
        a15Pack_extend _ a15PolyLength _ hshifted (by omega)
      rw [a15PolyProd, a15PolyStep, ih (by omega), a15Pack_shiftLeft, hcut,
        a15Pack_add]
      rfl

/-- Digits of the generating function are its coefficients. -/
theorem a15Digit_polyProd (S : ℕ → ℕ) (hS : ∀ i, S i ≤ 34) (n : ℕ) (hn : n ≤ 16)
    (v : ℕ) (hv : v < a15PolyLength) :
    a15Digit (a15PolyProd S n) v = a15PolyCoeff S n v := by
  rw [a15PolyProd_eq_pack S hS n hn,
    a15Digit_pack _ (fun w => a15PolyCoeff_lt_base S n w hn), if_pos hv]

/-! ### The subset counts -/

/-- Number of empty index subsets with shifted sum `v`. -/
def a15Q0 (v : ℕ) : ℕ := if v = 0 then 1 else 0

/-- Number of indices `i < n` with `S i = v`. -/
def a15Q1 (S : ℕ → ℕ) (v n : ℕ) : ℕ :=
  (List.range n).countP (fun i => S i == v)

/-- Number of pairs `i < j < n` with shifted sum `v`. -/
def a15Q2 (S : ℕ → ℕ) (v n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, (List.range j).countP (fun i => S i + S j == v)

/-- Number of triples `i < j < k < n` with shifted sum `v`. -/
def a15Q3 (S : ℕ → ℕ) (v n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range k,
    (List.range j).countP (fun i => S i + S j + S k == v)

/-- Number of quadruples `i < j < k < l < n` with shifted sum `v`, generated
in the order the fast counter visits them. -/
def a15Q4 (S : ℕ → ℕ) (v n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, ∑ l ∈ Finset.Ico (k + 1) n, ∑ j ∈ Finset.range k,
    (List.range j).countP (fun i => S i + S j + S k + S l == v)

theorem a15_countP_range_succ (n : ℕ) (p : ℕ → Bool) :
    (List.range (n + 1)).countP p =
      (List.range n).countP p + (if p n then 1 else 0) := by
  rw [List.range_succ, List.countP_append]
  simp only [List.countP_singleton]

theorem a15Q1_succ (S : ℕ → ℕ) (v n : ℕ) :
    a15Q1 S v (n + 1) =
      a15Q1 S v n + (if S n ≤ v then a15Q0 (v - S n) else 0) := by
  rw [a15Q1, a15Q1, a15_countP_range_succ]
  congr 1
  unfold a15Q0
  by_cases h : S n ≤ v
  · rw [if_pos h]
    by_cases h2 : S n = v
    · rw [if_pos (by simp [h2]), if_pos (by omega)]
    · rw [if_neg (by simp [h2]), if_neg (by omega)]
  · rw [if_neg h, if_neg (by simp; omega)]

theorem a15_countP_shift (n b v : ℕ) (F : ℕ → ℕ) :
    (List.range n).countP (fun i => F i + b == v) =
      if b ≤ v then (List.range n).countP (fun i => F i == v - b) else 0 := by
  by_cases h : b ≤ v
  · rw [if_pos h]
    refine List.countP_congr ?_
    intro i _
    simp only [beq_iff_eq]
    omega
  · rw [if_neg h]
    refine List.countP_eq_zero.mpr ?_
    intro i _
    simp only [beq_iff_eq]
    omega

theorem a15Q2_succ (S : ℕ → ℕ) (v n : ℕ) :
    a15Q2 S v (n + 1) =
      a15Q2 S v n + (if S n ≤ v then a15Q1 S (v - S n) n else 0) := by
  rw [a15Q2, a15Q2, Finset.sum_range_succ]
  congr 1
  exact a15_countP_shift n (S n) v (fun i => S i)

theorem a15Q3_succ (S : ℕ → ℕ) (v n : ℕ) :
    a15Q3 S v (n + 1) =
      a15Q3 S v n + (if S n ≤ v then a15Q2 S (v - S n) n else 0) := by
  rw [a15Q3, a15Q3, Finset.sum_range_succ]
  congr 1
  by_cases h : S n ≤ v
  · rw [if_pos h, a15Q2]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [a15_countP_shift j (S n) v (fun i => S i + S j), if_pos h]
  · rw [if_neg h]
    refine Finset.sum_eq_zero ?_
    intro j _
    rw [a15_countP_shift j (S n) v (fun i => S i + S j), if_neg h]

theorem a15Q4_succ (S : ℕ → ℕ) (v n : ℕ) :
    a15Q4 S v (n + 1) =
      a15Q4 S v n + (if S n ≤ v then a15Q3 S (v - S n) n else 0) := by
  rw [a15Q4, a15Q4, Finset.sum_range_succ]
  rw [show Finset.Ico (n + 1) (n + 1) = (∅ : Finset ℕ) from Finset.Ico_self _]
  rw [Finset.sum_empty, Nat.add_zero]
  have hsplit : ∀ k ∈ Finset.range n,
      (∑ l ∈ Finset.Ico (k + 1) (n + 1), ∑ j ∈ Finset.range k,
          (List.range j).countP (fun i => S i + S j + S k + S l == v)) =
        (∑ l ∈ Finset.Ico (k + 1) n, ∑ j ∈ Finset.range k,
          (List.range j).countP (fun i => S i + S j + S k + S l == v)) +
        ∑ j ∈ Finset.range k,
          (List.range j).countP (fun i => S i + S j + S k + S n == v) := by
    intro k hk
    have hkn : k + 1 ≤ n := Finset.mem_range.mp hk
    exact Finset.sum_Ico_succ_top hkn _
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  by_cases h : S n ≤ v
  · rw [if_pos h, a15Q3]
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [a15_countP_shift j (S n) v (fun i => S i + S j + S k), if_pos h]
  · rw [if_neg h]
    refine Finset.sum_eq_zero ?_
    intro k _
    refine Finset.sum_eq_zero ?_
    intro j _
    rw [a15_countP_shift j (S n) v (fun i => S i + S j + S k), if_neg h]

/-! ### Subset counts vanish beyond the maximal shifted sum -/

theorem a15Q1_eq_zero (S : ℕ → ℕ) (hS : ∀ i, S i ≤ 34) (v n : ℕ) (hv : 34 < v) :
    a15Q1 S v n = 0 := by
  refine List.countP_eq_zero.mpr ?_
  intro i _
  simp only [beq_iff_eq]
  have := hS i
  omega

theorem a15Q2_eq_zero (S : ℕ → ℕ) (hS : ∀ i, S i ≤ 34) (v n : ℕ) (hv : 68 < v) :
    a15Q2 S v n = 0 := by
  refine Finset.sum_eq_zero ?_
  intro j _
  refine List.countP_eq_zero.mpr ?_
  intro i _
  simp only [beq_iff_eq]
  have := hS i
  have := hS j
  omega

theorem a15Q3_eq_zero (S : ℕ → ℕ) (hS : ∀ i, S i ≤ 34) (v n : ℕ) (hv : 102 < v) :
    a15Q3 S v n = 0 := by
  refine Finset.sum_eq_zero ?_
  intro k _
  refine Finset.sum_eq_zero ?_
  intro j _
  refine List.countP_eq_zero.mpr ?_
  intro i _
  simp only [beq_iff_eq]
  have := hS i
  have := hS j
  have := hS k
  omega

/-! ### The ladder -/

theorem a15PolyCoeff_slot0 (S : ℕ → ℕ) (hS : ∀ i, S i ≤ 34) :
    ∀ (n v : ℕ), v < a15PolySlot → a15PolyCoeff S n v = a15Q0 v := by
  have hslot : a15PolySlot = 576 := rfl
  intro n
  induction n with
  | zero => intro v _; rfl
  | succ n ih =>
      intro v hv
      have hSn := hS n
      rw [a15PolyCoeff_succ, ih v hv, if_neg (by omega), Nat.add_zero]

theorem a15PolyCoeff_slot1 (S : ℕ → ℕ) (hS : ∀ i, S i ≤ 34) :
    ∀ (n v : ℕ), v < a15PolySlot →
      a15PolyCoeff S n (a15PolySlot + v) = a15Q1 S v n := by
  have hslot : a15PolySlot = 576 := rfl
  intro n
  induction n with
  | zero =>
      intro v _
      show (if a15PolySlot + v = 0 then 1 else 0) = a15Q1 S v 0
      rw [if_neg (by omega), a15Q1]
      simp
  | succ n ih =>
      intro v hv
      have hSn := hS n
      rw [a15PolyCoeff_succ, ih v hv, a15Q1_succ]
      congr 1
      by_cases h : S n ≤ v
      · rw [if_pos (by omega), if_pos h,
          show a15PolySlot + v - (a15PolySlot + S n) = v - S n by omega,
          a15PolyCoeff_slot0 S hS n _ (by omega)]
      · rw [if_neg (by omega), if_neg h]

theorem a15PolyCoeff_slot2 (S : ℕ → ℕ) (hS : ∀ i, S i ≤ 34) :
    ∀ (n v : ℕ), v < a15PolySlot →
      a15PolyCoeff S n (2 * a15PolySlot + v) = a15Q2 S v n := by
  have hslot : a15PolySlot = 576 := rfl
  intro n
  induction n with
  | zero =>
      intro v _
      show (if 2 * a15PolySlot + v = 0 then 1 else 0) = a15Q2 S v 0
      rw [if_neg (by omega), a15Q2]
      simp
  | succ n ih =>
      intro v hv
      have hSn := hS n
      rw [a15PolyCoeff_succ, ih v hv, a15Q2_succ, if_pos (by omega)]
      congr 1
      by_cases h : S n ≤ v
      · rw [if_pos h,
          show 2 * a15PolySlot + v - (a15PolySlot + S n) = a15PolySlot + (v - S n) by
            omega,
          a15PolyCoeff_slot1 S hS n _ (by omega)]
      · rw [if_neg h,
          show 2 * a15PolySlot + v - (a15PolySlot + S n) = a15PolySlot + v - S n by
            omega,
          a15PolyCoeff_slot0 S hS n _ (by omega), a15Q0, if_neg (by omega)]

theorem a15PolyCoeff_slot3 (S : ℕ → ℕ) (hS : ∀ i, S i ≤ 34) :
    ∀ (n v : ℕ), v < a15PolySlot →
      a15PolyCoeff S n (3 * a15PolySlot + v) = a15Q3 S v n := by
  have hslot : a15PolySlot = 576 := rfl
  intro n
  induction n with
  | zero =>
      intro v _
      show (if 3 * a15PolySlot + v = 0 then 1 else 0) = a15Q3 S v 0
      rw [if_neg (by omega), a15Q3]
      simp
  | succ n ih =>
      intro v hv
      have hSn := hS n
      rw [a15PolyCoeff_succ, ih v hv, a15Q3_succ, if_pos (by omega)]
      congr 1
      by_cases h : S n ≤ v
      · rw [if_pos h,
          show 3 * a15PolySlot + v - (a15PolySlot + S n) =
              2 * a15PolySlot + (v - S n) by omega,
          a15PolyCoeff_slot2 S hS n _ (by omega)]
      · rw [if_neg h,
          show 3 * a15PolySlot + v - (a15PolySlot + S n) =
              a15PolySlot + (a15PolySlot + v - S n) by omega,
          a15PolyCoeff_slot1 S hS n _ (by omega),
          a15Q1_eq_zero S hS _ n (by omega)]

theorem a15PolyCoeff_slot4 (S : ℕ → ℕ) (hS : ∀ i, S i ≤ 34) :
    ∀ (n v : ℕ), v < a15PolySlot →
      a15PolyCoeff S n (4 * a15PolySlot + v) = a15Q4 S v n := by
  have hslot : a15PolySlot = 576 := rfl
  intro n
  induction n with
  | zero =>
      intro v _
      show (if 4 * a15PolySlot + v = 0 then 1 else 0) = a15Q4 S v 0
      rw [if_neg (by omega), a15Q4]
      simp
  | succ n ih =>
      intro v hv
      have hSn := hS n
      rw [a15PolyCoeff_succ, ih v hv, a15Q4_succ, if_pos (by omega)]
      congr 1
      by_cases h : S n ≤ v
      · rw [if_pos h,
          show 4 * a15PolySlot + v - (a15PolySlot + S n) =
              3 * a15PolySlot + (v - S n) by omega,
          a15PolyCoeff_slot3 S hS n _ (by omega)]
      · rw [if_neg h,
          show 4 * a15PolySlot + v - (a15PolySlot + S n) =
              2 * a15PolySlot + (a15PolySlot + v - S n) by omega,
          a15PolyCoeff_slot2 S hS n _ (by omega),
          a15Q2_eq_zero S hS _ n (by omega)]


/-! ### Slot four is the slice decomposition of the fast counter -/

/-- The quadruple count over sixteen indices splits into the thirteen slices
the fast counter accumulates. -/
theorem a15Q4_eq_sliceSum (S : ℕ → ℕ) (v : ℕ) :
    a15Q4 S v 16 = ∑ i ∈ Finset.range 13, a15SliceCount S v (2 + i) := by
  have hslice : ∀ k : ℕ,
      (∑ l ∈ Finset.Ico (k + 1) 16, ∑ j ∈ Finset.range k,
          (List.range j).countP (fun i => S i + S j + S k + S l == v)) =
        a15SliceCount S v k := by
    intro k
    rw [Finset.sum_Ico_eq_sum_range, a15SliceCount,
      show 16 - (k + 1) = 15 - k by omega]
  have hsum : a15Q4 S v 16 = ∑ k ∈ Finset.range 16, a15SliceCount S v k := by
    rw [a15Q4]
    exact Finset.sum_congr rfl fun k _ => hslice k
  have h15 : a15SliceCount S v 15 = 0 := by
    rw [a15SliceCount]
    simp
  have h0 : a15SliceCount S v 0 = 0 := by
    rw [a15SliceCount]
    simp
  have h1 : a15SliceCount S v 1 = 0 := by
    rw [a15SliceCount]
    simp
  have hlow : ∑ i ∈ Finset.Ico 0 2, a15SliceCount S v i = 0 := by
    rw [show Finset.Ico 0 2 = Finset.range 2 from (Finset.range_eq_Ico 2).symm,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1]
  have hhigh : ∑ i ∈ Finset.Ico 2 15, a15SliceCount S v i =
      ∑ i ∈ Finset.range 13, a15SliceCount S v (2 + i) := by
    rw [Finset.sum_Ico_eq_sum_range]
  rw [hsum, Finset.sum_range_succ, h15, Nat.add_zero, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive (a15SliceCount S v) (Nat.zero_le 2)
      (by omega : (2 : ℕ) ≤ 15), hlow, hhigh, Nat.zero_add]

/-! ### The computable counter -/

/-- Eligible-shell counter based on the packed generating function.  The two
target digits are the shifted subset sums `15 - r + 68` and `-15 - r + 68`,
exactly the two target bases the fast byte counter uses. -/
def a15PolyEligibleCountReduced (residue : ℤ) (coordinates : List ℤ) : ℕ :=
  let p := a15PolyProd (a15ShiftedCoord coordinates) 16
  a15Digit p (4 * a15PolySlot + (if residue = 0 then 83 else 81)) +
    a15Digit p (4 * a15PolySlot + (if residue = 0 then 53 else 51))

theorem a15ShiftedCoord_le (coordinates : List ℤ)
    (hb : ∀ z ∈ coordinates, -17 ≤ z ∧ z ≤ 17) (i : ℕ) :
    a15ShiftedCoord coordinates i ≤ 34 := by
  rw [a15ShiftedCoord]
  by_cases hi : i < coordinates.length
  · rw [List.getD_eq_getElem coordinates 0 hi]
    have := hb _ (List.getElem_mem hi)
    omega
  · rw [List.getD_eq_default _ _ (by omega)]
    norm_num

theorem a15ShiftedCoord_val (coordinates : List ℤ)
    (hb : ∀ z ∈ coordinates, -17 ≤ z ∧ z ≤ 17) (i : ℕ)
    (hi : i < coordinates.length) :
    ((a15ShiftedCoord coordinates i : ℕ) : ℤ) = coordinates.getD i 0 + 17 := by
  rw [a15ShiftedCoord, List.getD_eq_getElem coordinates 0 hi]
  have := hb _ (List.getElem_mem hi)
  omega

/-- The generating-function counter is the reference count. -/
theorem a15PolyEligibleCountReduced_eq_exact (residue : ℤ)
    (hres : residue = 0 ∨ residue = 2) (coordinates : List ℤ)
    (hlen : coordinates.length = 16)
    (hb : ∀ z ∈ coordinates, -17 ≤ z ∧ z ≤ 17) :
    a15PolyEligibleCountReduced residue coordinates =
      a15ExactEligibleCardReduced residue coordinates := by
  set S : ℕ → ℕ := a15ShiftedCoord coordinates with hSdef
  have hS : ∀ i, S i ≤ 34 := a15ShiftedCoord_le coordinates hb
  have hSval : ∀ i, i < 16 → (S i : ℤ) = coordinates.getD i 0 + 17 := by
    intro i hi
    exact a15ShiftedCoord_val coordinates hb i (by omega)
  set tb1 : ℕ := if residue = 0 then 83 else 81 with htb1
  set tb2 : ℕ := if residue = 0 then 53 else 51 with htb2
  have htb1lt : tb1 < a15PolySlot := by
    rw [htb1]; split <;> norm_num [a15PolySlot]
  have htb2lt : tb2 < a15PolySlot := by
    rw [htb2]; split <;> norm_num [a15PolySlot]
  have hdigit : ∀ tb : ℕ, tb < a15PolySlot →
      a15Digit (a15PolyProd S 16) (4 * a15PolySlot + tb) = a15Q4 S tb 16 := by
    intro tb htb
    rw [a15Digit_polyProd S hS 16 (le_refl 16) _
        (by simp only [a15PolySlot, a15PolyLength] at htb ⊢; omega),
      a15PolyCoeff_slot4 S hS 16 tb htb]
  have hlhs : a15PolyEligibleCountReduced residue coordinates =
      a15Q4 S tb1 16 + a15Q4 S tb2 16 := by
    rw [a15PolyEligibleCountReduced, ← hSdef, ← htb1, ← htb2,
      hdigit tb1 htb1lt, hdigit tb2 htb2lt]
  have hexact : a15ExactEligibleCardReduced residue coordinates =
      ∑ i ∈ Finset.range 13,
        (a15SliceCount S tb1 (2 + i) + a15SliceCount S tb2 (2 + i)) := by
    rw [a15ExactEligibleCardReduced_eq_countP]
    have hdisj : ∀ s ∈ a15FourSubsetData.toList,
        ¬ (decide (a15ReducedDataSubsetSum coordinates s = 15 - residue) = true ∧
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
  rw [hlhs, hexact, Finset.sum_add_distrib, a15Q4_eq_sliceSum, a15Q4_eq_sliceSum]

/-- The generating-function counter and the fast byte counter answer the
enumerator's threshold question identically. -/
theorem a15_poly_fast_agree (residue : ℤ) (hres : residue = 0 ∨ residue = 2)
    (coordinates : List ℤ) (hlen : coordinates.length = 16)
    (hb : ∀ z ∈ coordinates, -17 ≤ z ∧ z ≤ 17) :
    (74 ≤ a15PolyEligibleCountReduced residue coordinates ↔
      74 ≤ a15FastEligibleCountReduced residue coordinates) := by
  rw [a15PolyEligibleCountReduced_eq_exact residue hres coordinates hlen hb]
  exact a15_counters_agree residue hres coordinates hlen hb

end SRG266
