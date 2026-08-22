/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15Plus

/-!
# Bounded kernel checker for the `A₁₅⁺` centroid certificates

The direct checker folds over the explicit array of 1,820 four-subsets for
every separator.  This module supplies an extensionally equal checker based
on the elementary include-or-skip recursion for choosing four coordinates
from sixteen.  Its recursion tree is small and fixed, so generated modules
can use kernel reduction with a predictable resource bound.
-/

open scoped BigOperators Matrix

namespace SRG266

@[ext]
structure A15FastTotals where
  eligible : ℕ
  support : ℤ
  deriving DecidableEq

instance : Zero A15FastTotals := ⟨⟨0, 0⟩⟩
instance : Add A15FastTotals :=
  ⟨fun a b => ⟨a.eligible + b.eligible, a.support + b.support⟩⟩

instance : AddCommMonoid A15FastTotals where
  add_assoc a b c := by
    apply A15FastTotals.ext
    · exact Nat.add_assoc _ _ _
    · exact Int.add_assoc _ _ _
  zero_add a := by
    apply A15FastTotals.ext
    · exact Nat.zero_add _
    · exact Int.zero_add _
  add_zero a := by
    apply A15FastTotals.ext
    · exact Nat.add_zero _
    · exact Int.add_zero _
  add_comm a b := by
    apply A15FastTotals.ext
    · exact Nat.add_comm _ _
    · exact Int.add_comm _ _
  nsmul := nsmulRec
  nsmul_zero := by intro x; rfl
  nsmul_succ := by intro n x; rfl

/-- Contribution of one selected four-subset. -/
def a15FastLeaf
    (countSeparator totalSeparator dSum qSum : ℤ) : A15FastTotals :=
  if dSum = -60 ∨ dSum = 60 then
    { eligible := 1
      support := integerPositivePart
        (countSeparator +
          if dSum = 60 then -(totalSeparator - 4 * qSum)
          else totalSeparator - 4 * qSum) }
  else 0

/-- Include-or-skip recursion choosing exactly `k` of the first `n`
coordinates. -/
def a15FastChoose
    (d q : ℕ → ℤ) (countSeparator totalSeparator : ℤ) :
    (n k : ℕ) → (dSum qSum : ℤ) → A15FastTotals
  | _, 0, dSum, qSum =>
      a15FastLeaf countSeparator totalSeparator dSum qSum
  | 0, _ + 1, _, _ => 0
  | n + 1, k + 1, dSum, qSum =>
      a15FastChoose d q countSeparator totalSeparator n (k + 1) dSum qSum +
        a15FastChoose d q countSeparator totalSeparator n k
          (dSum + d n) (qSum + q n)

def a15FastSubsetSum (f : ℕ → ℤ) (S : Finset ℕ) : ℤ :=
  ∑ i ∈ S, f i

theorem a15FastChoose_eq_powersetCard_sum
    (d q : ℕ → ℤ) (countSeparator totalSeparator : ℤ)
    (n k : ℕ) (dSum qSum : ℤ) :
    a15FastChoose d q countSeparator totalSeparator n k dSum qSum =
      ∑ S ∈ (Finset.range n).powersetCard k,
        a15FastLeaf countSeparator totalSeparator
          (dSum + a15FastSubsetSum d S)
          (qSum + a15FastSubsetSum q S) := by
  induction n generalizing k dSum qSum with
  | zero =>
      cases k with
      | zero => simp [a15FastChoose, a15FastSubsetSum]
      | succ k =>
          rw [Finset.powersetCard_eq_empty.mpr (by simp)]
          simp [a15FastChoose]
  | succ n ih =>
      cases k with
      | zero => simp [a15FastChoose, a15FastSubsetSum]
      | succ k =>
          rw [a15FastChoose, Finset.range_add_one,
            Finset.powersetCard_succ_insert (by simp) k]
          have hdisjoint :
              Disjoint ((Finset.range n).powersetCard (k + 1))
                (((Finset.range n).powersetCard k).image (insert n)) := by
            rw [Finset.disjoint_left]
            intro S hS hImage
            obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hImage
            have hsubset := (Finset.mem_powersetCard.mp hS).1
            exact (Finset.notMem_range_self : n ∉ Finset.range n)
              (hsubset (Finset.mem_insert_self n T))
          rw [Finset.sum_union hdisjoint]
          rw [ih (k + 1) dSum qSum]
          congr 1
          rw [ih k (dSum + d n) (qSum + q n)]
          rw [Finset.sum_image]
          · apply Finset.sum_congr rfl
            intro S hS
            have hn : n ∉ S := by
              have hsubset := (Finset.mem_powersetCard.mp hS).1
              exact fun hn =>
                (Finset.notMem_range_self : n ∉ Finset.range n) (hsubset hn)
            simp only [a15FastSubsetSum, Finset.sum_insert hn]
            congr 1 <;> ring
          · intro S hS T hT hST
            have hnS : n ∉ S := by
              have hsubset := (Finset.mem_powersetCard.mp hS).1
              exact fun hn =>
                (Finset.notMem_range_self : n ∉ Finset.range n) (hsubset hn)
            have hnT : n ∉ T := by
              have hsubset := (Finset.mem_powersetCard.mp hT).1
              exact fun hn =>
                (Finset.notMem_range_self : n ∉ Finset.range n) (hsubset hn)
            have hErase := congrArg (Finset.erase · n) hST
            simpa [hnS, hnT] using hErase

/-- Convert a subset of the range `0, ..., 15` to a subset of `Fin 16`. -/
def a15RangeSubset (S : Finset ℕ) : Finset (Fin 16) :=
  S.image a15FourSubsetCoordinate

theorem a15FourSubsetCoordinate_injectiveOn_range :
    Set.InjOn a15FourSubsetCoordinate (↑(Finset.range 16) : Set ℕ) := by
  intro i hi j hj hij
  have hi16 : i < 16 := Finset.mem_range.mp hi
  have hj16 : j < 16 := Finset.mem_range.mp hj
  have hval := congrArg Fin.val hij
  simpa [a15FourSubsetCoordinate, Nat.mod_eq_of_lt hi16,
    Nat.mod_eq_of_lt hj16] using hval

theorem a15RangeSubset_injectiveOn_fourSubsets :
    Set.InjOn a15RangeSubset
      (↑((Finset.range 16).powersetCard 4) : Set (Finset ℕ)) := by
  intro S hS T hT hST
  have hSsub := (Finset.mem_powersetCard.mp hS).1
  have hTsub := (Finset.mem_powersetCard.mp hT).1
  ext i
  constructor
  · intro hi
    have himage : a15FourSubsetCoordinate i ∈ a15RangeSubset S := by
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [hST] at himage
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp himage
    have hij : i = j := a15FourSubsetCoordinate_injectiveOn_range
      (hSsub hi) (hTsub hj) hji.symm
    simpa [hij] using hj
  · intro hi
    have himage : a15FourSubsetCoordinate i ∈ a15RangeSubset T := by
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [← hST] at himage
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp himage
    have hij : i = j := a15FourSubsetCoordinate_injectiveOn_range
      (hTsub hi) (hSsub hj) hji.symm
    simpa [hij] using hj

theorem a15RangeSubset_fourSubsetUniverse :
    ((Finset.range 16).powersetCard 4).image a15RangeSubset =
      Finset.univ.powersetCard 4 := by
  ext U
  constructor
  · intro hU
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hU
    rw [Finset.mem_powersetCard]
    constructor
    · simp [a15RangeSubset]
    · rw [a15RangeSubset, Finset.card_image_iff.mpr]
      · exact (Finset.mem_powersetCard.mp hS).2
      · exact a15FourSubsetCoordinate_injectiveOn_range.mono
          (Finset.mem_powersetCard.mp hS).1
  · intro hU
    let S : Finset ℕ := U.image Fin.val
    have hSsub : S ⊆ Finset.range 16 := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr j.isLt
    have hScard : S.card = 4 := by
      change (U.image Fin.val).card = 4
      rw [Finset.card_image_of_injective]
      · exact (Finset.mem_powersetCard.mp hU).2
      · exact Fin.val_injective
    apply Finset.mem_image.mpr
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨hSsub, hScard⟩, ?_⟩
    ext i
    simp only [a15RangeSubset, S, Finset.mem_image]
    constructor
    · rintro ⟨n, ⟨j, hj, rfl⟩, rfl⟩
      simpa [a15FourSubsetCoordinate, Nat.mod_eq_of_lt j.isLt] using hj
    · intro hi
      refine ⟨i.1, ⟨i, hi, rfl⟩, ?_⟩
      apply Fin.ext
      simp [a15FourSubsetCoordinate, Nat.mod_eq_of_lt i.isLt]

theorem a15FastSubsetSum_rangeSubset
    (f : Fin 16 → ℤ) (S : Finset ℕ) (hS : S ⊆ Finset.range 16) :
    a15FastSubsetSum (fun n => f (a15FourSubsetCoordinate n)) S =
      ∑ i ∈ a15RangeSubset S, f i := by
  rw [a15RangeSubset, Finset.sum_image]
  · rfl
  · exact a15FourSubsetCoordinate_injectiveOn_range.mono hS

private def a15FastSetContribution
    (d : Fin 16 → ℤ) (q : A15CentroidRow → ℤ)
    (S : Finset (Fin 16)) : A15FastTotals :=
  a15FastLeaf (q .count) (∑ i, q (.coordinate i))
    (∑ i ∈ S, d i) (∑ i ∈ S, q (.coordinate i))

theorem a15FastChoose_root_eq_finset_sum
    (d : Fin 16 → ℤ) (q : A15CentroidRow → ℤ) :
    a15FastChoose
        (fun n => d (a15FourSubsetCoordinate n))
        (fun n => q (.coordinate (a15FourSubsetCoordinate n)))
        (q .count) (∑ i, q (.coordinate i)) 16 4 0 0 =
      ∑ S ∈ Finset.univ.powersetCard 4,
        a15FastSetContribution d q S := by
  rw [a15FastChoose_eq_powersetCard_sum]
  simp only [zero_add]
  have hpoint : ∀ S ∈ (Finset.range 16).powersetCard 4,
      a15FastLeaf (q .count) (∑ i, q (.coordinate i))
          (a15FastSubsetSum (fun n => d (a15FourSubsetCoordinate n)) S)
          (a15FastSubsetSum
            (fun n => q (.coordinate (a15FourSubsetCoordinate n))) S) =
        a15FastSetContribution d q (a15RangeSubset S) := by
    intro S hS
    have hsub := (Finset.mem_powersetCard.mp hS).1
    unfold a15FastSetContribution
    rw [a15FastSubsetSum_rangeSubset d S hsub,
      a15FastSubsetSum_rangeSubset (fun i => q (.coordinate i)) S hsub]
  calc
    _ = ∑ S ∈ (Finset.range 16).powersetCard 4,
        a15FastSetContribution d q (a15RangeSubset S) := by
      apply Finset.sum_congr rfl
      exact hpoint
    _ = ∑ S ∈ ((Finset.range 16).powersetCard 4).image a15RangeSubset,
        a15FastSetContribution d q S := by
      rw [Finset.sum_image]
      exact a15RangeSubset_injectiveOn_fourSubsets
    _ = _ := by rw [a15RangeSubset_fourSubsetUniverse]

theorem a15FastSetContribution_indexed
    (d : Fin 16 → ℤ) (q : A15CentroidRow → ℤ)
    (s : A15FourSubsetIndex) :
    a15FastSetContribution d q (a15FourSubsetAsFinset s) =
      { eligible := if a15Eligible d s then 1 else 0
        support := if a15Eligible d s then
          integerPositivePart (a15RawColumnDot d q s) else 0 } := by
  unfold a15FastSetContribution
  rw [← a15FourSubset_valueSum_eq_finset_sum d s,
    ← a15FourSubset_valueSum_eq_finset_sum (fun i => q (.coordinate i)) s]
  unfold a15FastLeaf a15Eligible a15RawColumnDot a15DataRawColumnDot
    a15DataEligible a15DataSubsetSum
  by_cases hPositive : (a15FourSubsetAt s).valueSum d = 60
  · simp [hPositive]
  · by_cases hNegative : (a15FourSubsetAt s).valueSum d = -60
    · simp [hNegative]
    · simp [hPositive, hNegative]
      rfl

theorem a15FastChoose_root_eq_index_sum
    (d : Fin 16 → ℤ) (q : A15CentroidRow → ℤ) :
    a15FastChoose
        (fun n => d (a15FourSubsetCoordinate n))
        (fun n => q (.coordinate (a15FourSubsetCoordinate n)))
        (q .count) (∑ i, q (.coordinate i)) 16 4 0 0 =
      ∑ s : A15FourSubsetIndex,
        { eligible := if a15Eligible d s then 1 else 0
          support := if a15Eligible d s then
            integerPositivePart (a15RawColumnDot d q s) else 0 } := by
  rw [a15FastChoose_root_eq_finset_sum]
  rw [← a15FourSubsetUniverse_complete]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro s hs
    exact a15FastSetContribution_indexed d q s
  · exact fun s _ t _ h => a15FourSubsetAsFinset_injective h

private theorem a15Kernel_sum_get
    {M : Type*} [AddCommMonoid M] (l : List A15FourSubset)
    (f : A15FourSubset → M) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  rw [List.ofFn_comp', List.ofFn_get]

private theorem a15Kernel_foldl_add
    (l : List A15FourSubset) (f : A15FourSubset → ℕ) (initial : ℕ) :
    l.foldl (fun total x => total + f x) initial =
      initial + (l.map f).sum := by
  induction l generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      omega

theorem a15EligibleCount_eq_sum (d : Fin 16 → ℤ) :
    a15EligibleCount d =
      ∑ s : A15FourSubsetIndex, if a15Eligible d s then 1 else 0 := by
  unfold a15EligibleCount a15EligibleCountIn
  rw [← Array.foldl_toList, a15Kernel_foldl_add]
  simp only [zero_add]
  rw [← a15Kernel_sum_get]
  rfl

/-- Fast totals for one compact certificate. -/
def A15CentroidRawCertificate.fastTotals
    (c : A15CentroidRawCertificate) : A15FastTotals :=
  let cert := c.toCertificate
  a15FastChoose
    (fun n => cert.d (a15FourSubsetCoordinate n))
    (fun n => cert.q (.coordinate (a15FourSubsetCoordinate n)))
    (cert.q .count) (∑ i, cert.q (.coordinate i)) 16 4 0 0

private def a15FastEligibleHom : A15FastTotals →+ ℕ where
  toFun t := t.eligible
  map_zero' := rfl
  map_add' _ _ := rfl

private def a15FastSupportHom : A15FastTotals →+ ℤ where
  toFun t := t.support
  map_zero' := rfl
  map_add' _ _ := rfl

theorem A15CentroidRawCertificate.fastTotals_eligible
    (c : A15CentroidRawCertificate) :
    c.fastTotals.eligible = a15EligibleCount c.toCertificate.d := by
  rw [a15EligibleCount_eq_sum]
  change a15FastEligibleHom c.fastTotals = _
  calc
    _ = a15FastEligibleHom
        (∑ s : A15FourSubsetIndex,
          { eligible := if a15Eligible c.toCertificate.d s then 1 else 0
            support := if a15Eligible c.toCertificate.d s then
              integerPositivePart
                (a15RawColumnDot c.toCertificate.d c.toCertificate.q s)
              else 0 }) :=
      congrArg a15FastEligibleHom
        (a15FastChoose_root_eq_index_sum
          c.toCertificate.d c.toCertificate.q)
    _ = ∑ s : A15FourSubsetIndex,
        a15FastEligibleHom
          { eligible := if a15Eligible c.toCertificate.d s then 1 else 0
            support := if a15Eligible c.toCertificate.d s then
              integerPositivePart
                (a15RawColumnDot c.toCertificate.d c.toCertificate.q s)
              else 0 } := by rw [map_sum]
    _ = _ := by rfl

theorem A15CentroidRawCertificate.fastTotals_support
    (c : A15CentroidRawCertificate) :
    c.fastTotals.support =
      a15PositiveSupportIn a15FourSubsetData
        c.toCertificate.d c.toCertificate.q := by
  rw [a15PositiveSupport_eq_sum]
  change a15FastSupportHom c.fastTotals = _
  calc
    _ = a15FastSupportHom
        (∑ s : A15FourSubsetIndex,
          { eligible := if a15Eligible c.toCertificate.d s then 1 else 0
            support := if a15Eligible c.toCertificate.d s then
              integerPositivePart
                (a15RawColumnDot c.toCertificate.d c.toCertificate.q s)
              else 0 }) :=
      congrArg a15FastSupportHom
        (a15FastChoose_root_eq_index_sum
          c.toCertificate.d c.toCertificate.q)
    _ = ∑ s : A15FourSubsetIndex,
        a15FastSupportHom
          { eligible := if a15Eligible c.toCertificate.d s then 1 else 0
            support := if a15Eligible c.toCertificate.d s then
              integerPositivePart
                (a15RawColumnDot c.toCertificate.d c.toCertificate.q s)
              else 0 } := by rw [map_sum]
    _ = _ := by rfl

/-- Resource-bounded Boolean checker for generated centroid separators. -/
def A15CentroidRawCertificate.fastCheck
    (c : A15CentroidRawCertificate) : Bool :=
  decide (c.d.size = 16 ∧ c.q.size = 17) &&
    decide
      ((∀ i, c.toCertificate.d i % 4 = c.reportedResidue) ∧
        (∑ i, c.toCertificate.d i) = 0 ∧
        integerDot c.toCertificate.d c.toCertificate.d = 4800 ∧
        c.fastTotals.eligible = c.reportedEligible ∧
        integerDot c.toCertificate.q
            (a15CentroidTarget c.toCertificate.d) -
              3 * c.fastTotals.support = c.reportedGap ∧
        0 < c.reportedGap)

theorem A15CentroidRawCertificate.fastCheck_implies_check
    (c : A15CentroidRawCertificate) (h : c.fastCheck = true) :
    c.check = true := by
  have hparts :
      decide (c.d.size = 16 ∧ c.q.size = 17) = true ∧
        decide
          ((∀ i, c.toCertificate.d i % 4 = c.reportedResidue) ∧
            (∑ i, c.toCertificate.d i) = 0 ∧
            integerDot c.toCertificate.d c.toCertificate.d = 4800 ∧
            c.fastTotals.eligible = c.reportedEligible ∧
            integerDot c.toCertificate.q
                (a15CentroidTarget c.toCertificate.d) -
                  3 * c.fastTotals.support = c.reportedGap ∧
            0 < c.reportedGap) = true := by
    simpa only [A15CentroidRawCertificate.fastCheck, Bool.and_eq_true] using h
  have hdims := of_decide_eq_true hparts.1
  have hmath := of_decide_eq_true hparts.2
  unfold A15CentroidRawCertificate.check
    A15CentroidRawCertificate.checkWithSubsets
  rw [show decide (c.d.size = 16 ∧ c.q.size = 17) = true from hparts.1]
  simp only [Bool.true_and, A15CentroidCertificate.checkWithSubsets]
  apply decide_eq_true
  constructor
  · exact ⟨hmath.1, hmath.2.1, hmath.2.2.1,
      c.fastTotals_eligible.symm.trans hmath.2.2.2.1⟩
  constructor
  · unfold a15FarkasGapIn
    rw [← c.fastTotals_support]
    exact hmath.2.2.2.2.1
  · exact hmath.2.2.2.2.2

theorem A15CentroidRawCertificate.no_bounded_solution_of_fastCheck
    (c : A15CentroidRawCertificate) (h : c.fastCheck = true) :
    ¬∃ m : A15EligibleIndex c.toCertificate.d → ℤ,
      (∀ s, 0 ≤ m s) ∧
      (∀ s, m s ≤ 3) ∧
      a15CentroidMatrix c.toCertificate.d *ᵥ m =
        a15CentroidTarget c.toCertificate.d :=
  c.no_bounded_solution (c.fastCheck_implies_check h)

/-- The same bounded four-subset counter for a profile that has no separator
attached to it. -/
def A15CentroidRawSurvivor.fastEligible
    (c : A15CentroidRawSurvivor) : ℕ :=
  (a15FastChoose
    (fun n => c.toSurvivor.d (a15FourSubsetCoordinate n))
    (fun _ => 0) 0 0 16 4 0 0).eligible

theorem A15CentroidRawSurvivor.fastEligible_eq
    (c : A15CentroidRawSurvivor) :
    c.fastEligible = a15EligibleCount c.toSurvivor.d := by
  rw [a15EligibleCount_eq_sum]
  change a15FastEligibleHom
      (a15FastChoose
        (fun n => c.toSurvivor.d (a15FourSubsetCoordinate n))
        (fun _ => 0) 0 0 16 4 0 0) = _
  calc
    _ = a15FastEligibleHom
        (∑ s : A15FourSubsetIndex,
          { eligible := if a15Eligible c.toSurvivor.d s then 1 else 0
            support := if a15Eligible c.toSurvivor.d s then
              integerPositivePart (a15RawColumnDot c.toSurvivor.d (fun _ => 0) s)
              else 0 }) :=
      congrArg a15FastEligibleHom
        (a15FastChoose_root_eq_index_sum c.toSurvivor.d (fun _ => 0))
    _ = ∑ s : A15FourSubsetIndex,
        a15FastEligibleHom
          { eligible := if a15Eligible c.toSurvivor.d s then 1 else 0
            support := if a15Eligible c.toSurvivor.d s then
              integerPositivePart (a15RawColumnDot c.toSurvivor.d (fun _ => 0) s)
              else 0 } := by rw [map_sum]
    _ = _ := by rfl

def A15CentroidRawSurvivor.fastCheck
    (c : A15CentroidRawSurvivor) : Bool :=
  decide (c.d.size = 16) &&
    decide
      ((∀ i, c.toSurvivor.d i % 4 = c.reportedResidue) ∧
        (∑ i, c.toSurvivor.d i) = 0 ∧
        integerDot c.toSurvivor.d c.toSurvivor.d = 4800 ∧
        c.fastEligible = c.reportedEligible)

theorem A15CentroidRawSurvivor.fastCheck_implies_check
    (c : A15CentroidRawSurvivor) (h : c.fastCheck = true) :
    c.check = true := by
  have hparts :
      decide (c.d.size = 16) = true ∧
        decide
          ((∀ i, c.toSurvivor.d i % 4 = c.reportedResidue) ∧
            (∑ i, c.toSurvivor.d i) = 0 ∧
            integerDot c.toSurvivor.d c.toSurvivor.d = 4800 ∧
            c.fastEligible = c.reportedEligible) = true := by
    simpa only [A15CentroidRawSurvivor.fastCheck, Bool.and_eq_true] using h
  have hmath := of_decide_eq_true hparts.2
  unfold A15CentroidRawSurvivor.check A15CentroidSurvivor.check
  rw [show decide (c.d.size = 16) = true from hparts.1]
  simp only [Bool.true_and]
  apply decide_eq_true
  exact ⟨hmath.1, hmath.2.1, hmath.2.2.1,
    c.fastEligible_eq.symm.trans hmath.2.2.2⟩

end SRG266
