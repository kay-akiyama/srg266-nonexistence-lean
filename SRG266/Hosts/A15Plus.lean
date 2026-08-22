/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.A15FourSubsets
import SRG266.Certificates.Farkas

/-!
# The finite `A₁₅⁺` centroid shell model

A norm-three shell vector is indexed by a four-subset `S` of 16 coordinates.
After multiplication by four its coordinates are

`a_S(i) = -3` for `i ∈ S`, and `a_S(i) = 1` otherwise.

For the integral centroid coordinate vector `d = 4c`, eligibility is the
four-subset equation `∑_{i ∈ S} d_i = ±60`. The sign of `a_S` is oriented so
that its pairing with `d` is positive. The resulting 17-row system has a
count row and 16 coordinate rows, with target `(220, 11d)`.

The theoretical matrix below is indexed by the complete finite shell. The
reflective checker traverses the same checked array directly, avoiding
reconstruction of the 1,820 combinations for each certificate.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000

theorem a15FourSubset_count :
    Fintype.card A15FourSubsetIndex = 1820 := by
  simp [a15FourSubsetData_size]

/-- Sum of coordinate values over one raw four-subset. -/
def a15DataSubsetSum
    (d : Fin 16 → ℤ) (s : A15FourSubset) : ℤ :=
  s.valueSum d

/-- Sum of centroid coordinates over an indexed four-subset. -/
def a15SubsetSum
    (d : Fin 16 → ℤ) (s : A15FourSubsetIndex) : ℤ :=
  a15DataSubsetSum d (a15FourSubsetAt s)

def a15DataEligible
    (d : Fin 16 → ℤ) (s : A15FourSubset) : Prop :=
  a15DataSubsetSum d s = -60 ∨ a15DataSubsetSum d s = 60

instance (d : Fin 16 → ℤ) (s : A15FourSubset) :
    Decidable (a15DataEligible d s) := by
  unfold a15DataEligible
  infer_instance

/-- Eligibility of a four-subset for the oriented norm-three shell. -/
def a15Eligible
    (d : Fin 16 → ℤ) (s : A15FourSubsetIndex) : Prop :=
  a15DataEligible d (a15FourSubsetAt s)

instance (d : Fin 16 → ℤ) : DecidablePred (a15Eligible d) :=
  fun s => by
    unfold a15Eligible
    infer_instance

/-- The eligible four-subsets for one centroid profile. -/
abbrev A15EligibleIndex (d : Fin 16 → ℤ) :=
  {s : A15FourSubsetIndex // a15Eligible d s}

instance (d : Fin 16 → ℤ) : Fintype (A15EligibleIndex d) :=
  Fintype.subtype
    (Finset.univ.filter (a15Eligible d))
    (by simp)

theorem a15FourSubset_valueSum_eq_finset_sum
    (f : Fin 16 → ℤ) (s : A15FourSubsetIndex) :
    (a15FourSubsetAt s).valueSum f =
      ∑ i ∈ a15FourSubsetAsFinset s, f i := by
  exact
    (List.sum_toFinset f
      (a15FourSubsetAt_coordinates_nodup s)).symm

/-- One coordinate of an oriented shell vector, with its subset data and
subset sum already computed. -/
def a15ShellCoordinate4
    (s : Finset (Fin 16)) (subsetSum : ℤ) (i : Fin 16) : ℤ :=
  let z : ℤ := if i ∈ s then -3 else 1
  if subsetSum = 60 then -z else z

/-- Four times the oriented shell vector associated with an eligible
four-subset. -/
def a15ShellVector4
    (d : Fin 16 → ℤ) (s : A15EligibleIndex d) (i : Fin 16) : ℤ :=
  a15ShellCoordinate4 (a15FourSubsetAsFinset s.1)
    (a15SubsetSum d s.1) i

/-- Rows of the A15 centroid system. -/
inductive A15CentroidRow
  | count
  | coordinate (i : Fin 16)
  deriving DecidableEq, Fintype

def a15CentroidRowEquiv :
    A15CentroidRow ≃ Unit ⊕ Fin 16 where
  toFun
    | .count => Sum.inl ()
    | .coordinate i => Sum.inr i
  invFun
    | Sum.inl _ => .count
    | Sum.inr i => .coordinate i
  left_inv r := by cases r <;> rfl
  right_inv r := by rcases r with (_ | i) <;> rfl

theorem a15CentroidRow_sum
    {R : Type*} [AddCommMonoid R] (f : A15CentroidRow → R) :
    ∑ r, f r = f .count + ∑ i, f (.coordinate i) := by
  calc
    _ = ∑ r : Unit ⊕ Fin 16, f (a15CentroidRowEquiv.symm r) :=
      (a15CentroidRowEquiv.symm.sum_comp f).symm
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [a15CentroidRowEquiv]

/-- The 17 by `#eligible` exact shell-column matrix. -/
def a15CentroidMatrix
    (d : Fin 16 → ℤ) :
    Matrix A15CentroidRow (A15EligibleIndex d) ℤ
  | .count, _ => 1
  | .coordinate i, s => a15ShellVector4 d s i

/-- The exact target `(220, 11d)` of the centroid equations. -/
def a15CentroidTarget
    (d : Fin 16 → ℤ) : A15CentroidRow → ℤ
  | .count => 220
  | .coordinate i => 11 * d i

/-- Number of eligible shell columns in a supplied subset universe. -/
def a15EligibleCountIn
    (subsets : Array A15FourSubset) (d : Fin 16 → ℤ) : ℕ :=
  subsets.foldl (fun count s =>
    count + if a15DataEligible d s then 1 else 0) 0

/-- Number of eligible shell columns regenerated from a centroid profile. -/
def a15EligibleCount (d : Fin 16 → ℤ) : ℕ :=
  a15EligibleCountIn a15FourSubsetData d

/-- Dot product of a separator with one raw shell column. -/
def a15DataRawColumnDot
    (d : Fin 16 → ℤ) (q : A15CentroidRow → ℤ)
    (s : A15FourSubset) : ℤ :=
  let subsetSum := a15DataSubsetSum d s
  let rawDot :=
    (∑ i, q (.coordinate i)) -
      4 * s.valueSum (fun i => q (.coordinate i))
  q .count + if subsetSum = 60 then -rawDot else rawDot

/-- Dot product of a separator with one indexed shell column. -/
def a15RawColumnDot
    (d : Fin 16 → ℤ) (q : A15CentroidRow → ℤ)
    (s : A15FourSubsetIndex) : ℤ :=
  a15DataRawColumnDot d q (a15FourSubsetAt s)

theorem a15_raw_coordinate_dot
    (q : A15CentroidRow → ℤ) (s : Finset (Fin 16)) :
    (∑ i, q (.coordinate i) * (if i ∈ s then -3 else 1)) =
      (∑ i, q (.coordinate i)) -
        4 * ∑ i ∈ s, q (.coordinate i) := by
  calc
    _ = ∑ i, (q (.coordinate i) -
        4 * if i ∈ s then q (.coordinate i) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases his : i ∈ s
      · simp [his]
        ring
      · simp [his]
    _ = (∑ i, q (.coordinate i)) -
        4 * ∑ i, if i ∈ s then q (.coordinate i) else 0 := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp

theorem a15RawColumnDot_eq_integerDot
    (d : Fin 16 → ℤ) (q : A15CentroidRow → ℤ)
    (s : A15EligibleIndex d) :
    a15RawColumnDot d q s.1 =
      integerDot q (fun r => a15CentroidMatrix d r s) := by
  rw [integerDot, a15CentroidRow_sum]
  simp only [a15CentroidMatrix, mul_one]
  by_cases hsum : a15SubsetSum d s.1 = 60
  · have hsum' :
        a15DataSubsetSum d (a15FourSubsetAt s.1) = 60 := by
      simpa only [a15SubsetSum] using hsum
    simp only [a15RawColumnDot, a15DataRawColumnDot, a15ShellVector4,
      a15ShellCoordinate4, hsum, hsum', ↓reduceIte]
    rw [a15FourSubset_valueSum_eq_finset_sum]
    have hneg :
        (∑ i, q (.coordinate i) *
            -(if i ∈ a15FourSubsetAsFinset s.1 then -3 else 1)) =
          -∑ i, q (.coordinate i) *
            (if i ∈ a15FourSubsetAsFinset s.1 then -3 else 1) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hneg, a15_raw_coordinate_dot]
  · have hsum' :
        a15DataSubsetSum d (a15FourSubsetAt s.1) ≠ 60 := by
      simpa only [a15SubsetSum] using hsum
    simp only [a15RawColumnDot, a15DataRawColumnDot, a15ShellVector4,
      a15ShellCoordinate4, hsum, hsum', ↓reduceIte]
    rw [a15FourSubset_valueSum_eq_finset_sum]
    apply congrArg (q .count + ·)
    exact (a15_raw_coordinate_dot q (a15FourSubsetAsFinset s.1)).symm

/-- Sum of positive separator-column pairings over a supplied universe. -/
def a15PositiveSupportIn
    (subsets : Array A15FourSubset)
    (d : Fin 16 → ℤ) (q : A15CentroidRow → ℤ) : ℤ :=
  subsets.foldl (fun total s =>
    total + if a15DataEligible d s then
      integerPositivePart (a15DataRawColumnDot d q s)
    else 0) 0

/-- Exact strict bounded Farkas gap in a supplied subset universe. -/
def a15FarkasGapIn
    (subsets : Array A15FourSubset)
    (d : Fin 16 → ℤ) (q : A15CentroidRow → ℤ) : ℤ :=
  integerDot q (a15CentroidTarget d) -
    3 * a15PositiveSupportIn subsets d q

/-- Exact strict bounded Farkas gap for one centroid profile. -/
def a15FarkasGap
    (d : Fin 16 → ℤ) (q : A15CentroidRow → ℤ) : ℤ :=
  a15FarkasGapIn a15FourSubsetData d q

private theorem a15_sum_get
    {α M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → M) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  rw [List.ofFn_comp', List.ofFn_get]

private theorem a15_foldl_add
    {α : Type*} (l : List α) (f : α → ℤ) (initial : ℤ) :
    l.foldl (fun total x => total + f x) initial =
      initial + (l.map f).sum := by
  induction l generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem a15PositiveSupport_eq_sum
    (d : Fin 16 → ℤ) (q : A15CentroidRow → ℤ) :
    a15PositiveSupportIn a15FourSubsetData d q =
      ∑ s : A15FourSubsetIndex,
        if a15Eligible d s then
          integerPositivePart (a15RawColumnDot d q s)
        else 0 := by
  unfold a15PositiveSupportIn
  rw [← Array.foldl_toList, a15_foldl_add]
  simp only [zero_add]
  rw [← a15_sum_get]
  rfl

theorem a15_no_bounded_solution_of_positive_gap
    (d : Fin 16 → ℤ) (q : A15CentroidRow → ℤ)
    (hgap : 0 < a15FarkasGap d q) :
    ¬∃ m : A15EligibleIndex d → ℤ,
      (∀ s, 0 ≤ m s) ∧
      (∀ s, m s ≤ 3) ∧
      a15CentroidMatrix d *ᵥ m = a15CentroidTarget d := by
  apply no_bounded_solution_of_farkas
    (a15CentroidMatrix d) (a15CentroidTarget d) q
  unfold BoundedFarkasSeparates
  unfold a15FarkasGap a15FarkasGapIn at hgap
  rw [a15PositiveSupport_eq_sum] at hgap
  have hsubtype :
      (∑ s : A15FourSubsetIndex,
          if a15Eligible d s then
            integerPositivePart (a15RawColumnDot d q s)
          else 0) =
        ∑ s : A15EligibleIndex d,
          integerPositivePart
            (integerDot q (fun r => a15CentroidMatrix d r s)) := by
    calc
      _ = ∑ s ∈ Finset.univ.filter (a15Eligible d),
          integerPositivePart (a15RawColumnDot d q s) := by
        rw [Finset.sum_filter]
      _ = ∑ s : A15EligibleIndex d,
          integerPositivePart (a15RawColumnDot d q s.1) := by
        apply Finset.sum_subtype
        intro s
        simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [a15RawColumnDot_eq_integerDot]
  rw [hsubtype] at hgap
  omega

/-- The exact profile conditions in a supplied subset universe. -/
def A15CentroidProfileValidIn
    (subsets : Array A15FourSubset)
    (d : Fin 16 → ℤ) (reportedResidue : ℤ)
    (reportedEligible : ℕ) : Prop :=
  (∀ i, d i % 4 = reportedResidue) ∧
  (∑ i, d i) = 0 ∧
  integerDot d d = 4800 ∧
  a15EligibleCountIn subsets d = reportedEligible

instance (subsets : Array A15FourSubset) (d : Fin 16 → ℤ)
    (reportedResidue : ℤ) (reportedEligible : ℕ) :
    Decidable
      (A15CentroidProfileValidIn subsets d
        reportedResidue reportedEligible) := by
  unfold A15CentroidProfileValidIn
  infer_instance

/-- The exact profile conditions recomputed for both rejected and surviving
canonical centroid profiles. -/
def A15CentroidProfileValid
    (d : Fin 16 → ℤ) (reportedResidue : ℤ)
    (reportedEligible : ℕ) : Prop :=
  A15CentroidProfileValidIn a15FourSubsetData d
    reportedResidue reportedEligible

instance (d : Fin 16 → ℤ) (reportedResidue : ℤ)
    (reportedEligible : ℕ) :
    Decidable (A15CentroidProfileValid d reportedResidue reportedEligible) := by
  unfold A15CentroidProfileValid
  infer_instance

/-- Declarative data for one rejected canonical A15 centroid profile.

The residue, norm, eligible count, and gap are recomputed by `check`; Python
supplies only the integer profile and separator. -/
structure A15CentroidCertificate where
  d : Fin 16 → ℤ
  q : A15CentroidRow → ℤ
  reportedResidue : ℤ
  reportedEligible : ℕ
  reportedGap : ℤ

/-- Check one certificate using an already materialized subset universe. -/
def A15CentroidCertificate.checkWithSubsets
    (subsets : Array A15FourSubset)
    (c : A15CentroidCertificate) : Bool :=
  decide (
    A15CentroidProfileValidIn subsets c.d
      c.reportedResidue c.reportedEligible ∧
    a15FarkasGapIn subsets c.d c.q = c.reportedGap ∧
    0 < c.reportedGap)

/-- Reflective checker for one A15 centroid separator. -/
def A15CentroidCertificate.check
    (c : A15CentroidCertificate) : Bool :=
  A15CentroidCertificate.checkWithSubsets a15FourSubsetData c

theorem A15CentroidCertificate.no_bounded_solution
    (c : A15CentroidCertificate) (hcheck : c.check = true) :
    ¬∃ m : A15EligibleIndex c.d → ℤ,
      (∀ s, 0 ≤ m s) ∧
      (∀ s, m s ≤ 3) ∧
      a15CentroidMatrix c.d *ᵥ m = a15CentroidTarget c.d := by
  have h := of_decide_eq_true (by
    simpa only [A15CentroidCertificate.check,
      A15CentroidCertificate.checkWithSubsets] using hcheck)
  apply a15_no_bounded_solution_of_positive_gap c.d c.q
  unfold a15FarkasGap
  omega

/-- Compact array representation used by generated separator data. -/
structure A15CentroidRawCertificate where
  d : Array ℤ
  q : Array ℤ
  reportedResidue : ℤ
  reportedEligible : ℕ
  reportedGap : ℤ

def A15CentroidRawCertificate.toCertificate
    (c : A15CentroidRawCertificate) : A15CentroidCertificate where
  d i := c.d.getD i.1 0
  q
    | .count => c.q.getD 0 0
    | .coordinate i => c.q.getD (i.1 + 1) 0
  reportedResidue := c.reportedResidue
  reportedEligible := c.reportedEligible
  reportedGap := c.reportedGap

/-- Check compact data after validating the two array dimensions. -/
def A15CentroidRawCertificate.checkWithSubsets
    (subsets : Array A15FourSubset)
    (c : A15CentroidRawCertificate) : Bool :=
  decide (c.d.size = 16 ∧ c.q.size = 17) &&
    c.toCertificate.checkWithSubsets subsets

def A15CentroidRawCertificate.check
    (c : A15CentroidRawCertificate) : Bool :=
  c.checkWithSubsets a15FourSubsetData

theorem A15CentroidRawCertificate.no_bounded_solution
    (c : A15CentroidRawCertificate) (hcheck : c.check = true) :
    ¬∃ m : A15EligibleIndex c.toCertificate.d → ℤ,
      (∀ s, 0 ≤ m s) ∧
      (∀ s, m s ≤ 3) ∧
      a15CentroidMatrix c.toCertificate.d *ᵥ m =
        a15CentroidTarget c.toCertificate.d := by
  apply c.toCertificate.no_bounded_solution
  have hparts :
      decide (c.d.size = 16 ∧ c.q.size = 17) = true ∧
        c.toCertificate.checkWithSubsets a15FourSubsetData = true := by
    simpa only [A15CentroidRawCertificate.check,
      A15CentroidRawCertificate.checkWithSubsets, Bool.and_eq_true] using
      hcheck
  simpa only [A15CentroidCertificate.check] using hparts.2

/-- Declarative data for one centroid profile that survives the supplied
Farkas separators. -/
structure A15CentroidSurvivor where
  d : Fin 16 → ℤ
  reportedResidue : ℤ
  reportedEligible : ℕ

/-- Recompute the norm-profile and eligible-column audit fields for a
survivor. -/
def A15CentroidSurvivor.check
    (c : A15CentroidSurvivor) : Bool :=
  decide
    (A15CentroidProfileValid c.d c.reportedResidue c.reportedEligible)

/-- Compact array representation of a surviving centroid profile. -/
structure A15CentroidRawSurvivor where
  d : Array ℤ
  reportedResidue : ℤ
  reportedEligible : ℕ

def A15CentroidRawSurvivor.toSurvivor
    (c : A15CentroidRawSurvivor) : A15CentroidSurvivor where
  d i := c.d.getD i.1 0
  reportedResidue := c.reportedResidue
  reportedEligible := c.reportedEligible

def A15CentroidRawSurvivor.check
    (c : A15CentroidRawSurvivor) : Bool :=
  decide (c.d.size = 16) && c.toSurvivor.check

end SRG266
