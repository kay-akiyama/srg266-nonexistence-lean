/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15Plus
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Orbit-averaged projectors for the `A₁₅⁺` shell

For a centroid profile `d`, equal coordinates split the 16 positions into
classes. The coordinate stabilizer partitions eligible four-subsets by their
orientation and by the number of selected positions in each class.

This module defines:

* a reflective audit of the orbit partition and its first and second moments;
* the exact rational averaged complement projector;
* the bounded orbit-total equations;
* negative quadratic-form and negative two-dimensional-minor witnesses.

Generated modules contain only profiles, moment tables, orbit totals, and
witness vectors. The checker recomputes the orbit tables from all 1,820
four-subsets before using them.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000

def a15ProjectorRawCoordinates (s : A15FourSubset) : List ℕ :=
  [s.a, s.b, s.c, s.d]

def a15ProjectorProfileCoordinate
    (d : Array ℤ) (i : Fin 16) : ℤ :=
  d.getD i.1 0

/-- Orientation used by the shell model: `1` for subset sum `-60`, `-1` for
subset sum `60`, and `0` for an ineligible subset. -/
def a15ProjectorSubsetSign
    (d : Array ℤ) (s : A15FourSubset) : ℤ :=
  let subsetSum := s.valueSum (a15ProjectorProfileCoordinate d)
  if subsetSum = -60 then 1 else if subsetSum = 60 then -1 else 0

def a15ProjectorShellCoordinate
    (d : Array ℤ) (s : A15FourSubset) (i : Fin 16) : ℤ :=
  a15ProjectorSubsetSign d s *
    if s.coordinates.contains i then -3 else 1

def a15ProjectorClassStart
    (classSizes : Array ℕ) (k : ℕ) : ℕ :=
  (classSizes.toList.take k).sum

def a15ProjectorClassCount
    (classSizes : Array ℕ) (s : A15FourSubset) (k : ℕ) : ℕ :=
  let first := a15ProjectorClassStart classSizes k
  let last := first + classSizes.getD k 0
  (a15ProjectorRawCoordinates s).countP fun i =>
    first ≤ i && i < last

/-- One coordinate-stabilizer orbit signature. -/
structure A15ProjectorOrbit where
  sign : ℤ
  classCounts : Array ℕ
  reportedSize : ℕ
  firstMoment : Array ℤ
  secondMoment : Array ℤ

def A15ProjectorOrbit.matches
    (classSizes : Array ℕ) (orbit : A15ProjectorOrbit)
    (d : Array ℤ) (s : A15FourSubset) : Bool :=
  decide (a15ProjectorSubsetSign d s = orbit.sign) &&
    decide (orbit.classCounts.size = classSizes.size) &&
    (List.range classSizes.size).all fun k =>
      decide
        (orbit.classCounts.getD k 0 =
          a15ProjectorClassCount classSizes s k)

structure A15ProjectorOrbitStats where
  size : ℕ
  firstMoment : Array ℤ
  secondMoment : Array ℤ
  deriving DecidableEq

def A15ProjectorOrbitStats.zero : A15ProjectorOrbitStats where
  size := 0
  firstMoment := Array.replicate 16 0
  secondMoment := Array.replicate 256 0

def A15ProjectorOrbitStats.addShell
    (stats : A15ProjectorOrbitStats)
    (d : Array ℤ) (s : A15FourSubset) : A15ProjectorOrbitStats where
  size := stats.size + 1
  firstMoment := stats.firstMoment.mapIdx fun i total =>
    total + a15ProjectorShellCoordinate d s
      ⟨i % 16, Nat.mod_lt i (by decide)⟩
  secondMoment := stats.secondMoment.mapIdx fun index total =>
    let i : Fin 16 :=
      ⟨(index / 16) % 16, Nat.mod_lt _ (by decide)⟩
    let j : Fin 16 :=
      ⟨index % 16, Nat.mod_lt _ (by decide)⟩
    total + a15ProjectorShellCoordinate d s i *
      a15ProjectorShellCoordinate d s j

def A15ProjectorOrbit.computedStats
    (classSizes : Array ℕ) (orbit : A15ProjectorOrbit)
    (d : Array ℤ) : A15ProjectorOrbitStats :=
  a15FourSubsetData.foldl (fun stats s =>
    if orbit.matches classSizes d s then stats.addShell d s else stats)
    A15ProjectorOrbitStats.zero

def A15ProjectorOrbit.check
    (classSizes : Array ℕ) (d : Array ℤ)
    (orbit : A15ProjectorOrbit) : Bool :=
  let computed := orbit.computedStats classSizes d
  decide (orbit.sign = -1 ∨ orbit.sign = 1) &&
    decide (orbit.classCounts.size = classSizes.size) &&
    decide (orbit.classCounts.toList.sum = 4) &&
    decide (orbit.firstMoment.size = 16) &&
    decide (orbit.secondMoment.size = 256) &&
    decide (computed =
      { size := orbit.reportedSize,
        firstMoment := orbit.firstMoment,
        secondMoment := orbit.secondMoment })

/-- A centroid profile together with its checked orbit moment tables. -/
structure A15ProjectorProfile where
  centroidIndex : ℕ
  d : Array ℤ
  reportedEligible : ℕ
  classValues : Array ℤ
  classSizes : Array ℕ
  orbits : Array A15ProjectorOrbit

def A15ProjectorProfile.expandedClasses
    (profile : A15ProjectorProfile) : List ℤ :=
  (profile.classValues.toList.zip profile.classSizes.toList).flatMap
    fun valueAndSize => List.replicate valueAndSize.2 valueAndSize.1

def A15ProjectorProfile.matchCount
    (profile : A15ProjectorProfile) (s : A15FourSubset) : ℕ :=
  profile.orbits.foldl (fun total orbit =>
    total + if orbit.matches profile.classSizes profile.d s then 1 else 0) 0

def A15ProjectorProfile.eligibleCount
    (profile : A15ProjectorProfile) : ℕ :=
  a15FourSubsetData.foldl (fun total s =>
    total + if a15ProjectorSubsetSign profile.d s = 0 then 0 else 1) 0

def A15ProjectorProfile.checkOrbitUniverse
    (profile : A15ProjectorProfile) : Bool :=
  decide (profile.d.size = 16) &&
    decide (profile.classValues.size = profile.classSizes.size) &&
    decide (profile.classSizes.toList.sum = 16) &&
    decide (profile.expandedClasses = profile.d.toList) &&
    decide (profile.eligibleCount = profile.reportedEligible) &&
    profile.orbits.all (A15ProjectorOrbit.check profile.classSizes profile.d) &&
    a15FourSubsetData.all fun s =>
      if a15ProjectorSubsetSign profile.d s = 0 then
        decide (profile.matchCount s = 0)
      else
        decide (profile.matchCount s = 1)

def A15ProjectorProfile.orbitFirstMoment
    (profile : A15ProjectorProfile) (k : ℕ) (i : Fin 16) : ℤ :=
  (profile.orbits.getD k
    { sign := 0, classCounts := #[], reportedSize := 0,
      firstMoment := #[], secondMoment := #[] }).firstMoment.getD i.1 0

def A15ProjectorProfile.orbitSecondMoment
    (profile : A15ProjectorProfile) (k : ℕ)
    (i j : Fin 16) : ℤ :=
  (profile.orbits.getD k
    { sign := 0, classCounts := #[], reportedSize := 0,
      firstMoment := #[], secondMoment := #[] }).secondMoment.getD
        (16 * i.1 + j.1) 0

def A15ProjectorProfile.orbitSize
    (profile : A15ProjectorProfile) (k : ℕ) : ℕ :=
  (profile.orbits.getD k
    { sign := 0, classCounts := #[], reportedSize := 0,
      firstMoment := #[], secondMoment := #[] }).reportedSize

def a15ProjectorListSumRat (l : List ℚ) : ℚ :=
  l.sum

/-- Exact entry of the averaged complement projector

`I - J/16 + ddᵀ/1800 - ∑ₒ Tₒ Aₒ/(720 |o|)`.
-/
def A15ProjectorProfile.projectorEntry
    (profile : A15ProjectorProfile) (totals : Array ℕ)
    (i j : Fin 16) : ℚ :=
  (if i = j then 1 else 0) - 1 / 16 +
    (profile.d.getD i.1 0 * profile.d.getD j.1 0 : ℚ) / 1800 -
    a15ProjectorListSumRat ((List.range profile.orbits.size).map fun k =>
      (totals.getD k 0 * profile.orbitSecondMoment k i j : ℚ) /
        (720 * profile.orbitSize k : ℚ))

def A15ProjectorProfile.projectorMatrix
    (profile : A15ProjectorProfile) (totals : Array ℕ) :
    Matrix (Fin 16) (Fin 16) ℚ :=
  profile.projectorEntry totals

def A15ProjectorProfile.orbitTotalsValid
    (profile : A15ProjectorProfile) (totals : Array ℕ) : Prop :=
  totals.size = profile.orbits.size ∧
  (∀ k : Fin profile.orbits.size,
    totals.getD k.1 0 ≤ 3 * profile.orbitSize k.1) ∧
  (∑ k : Fin profile.orbits.size, totals.getD k.1 0) = 220 ∧
  ∀ i : Fin 16,
    (∑ k : Fin profile.orbits.size,
      (totals.getD k.1 0 * profile.orbitFirstMoment k.1 i : ℚ) /
        (profile.orbitSize k.1 : ℚ)) =
      11 * profile.d.getD i.1 0

instance (profile : A15ProjectorProfile) (totals : Array ℕ) :
    Decidable (profile.orbitTotalsValid totals) := by
  unfold A15ProjectorProfile.orbitTotalsValid
  infer_instance

def A15ProjectorProfile.orbitAverage
    (profile : A15ProjectorProfile)
    (k : Fin profile.orbits.size) (i : Fin 16) : ℚ :=
  (profile.orbitFirstMoment k.1 i : ℚ) /
    (profile.orbitSize k.1 : ℚ)

/-- An exact rational linear combination of the count and centroid rows. -/
structure A15OrbitRelation where
  coefficients : Array ℤ
  constant : ℤ
  multipliers : Array ℚ
  deriving Inhabited

def A15OrbitRelation.multiplier
    (relation : A15OrbitRelation) : A15CentroidRow → ℚ
  | .count => relation.multipliers.getD 0 0
  | .coordinate i => relation.multipliers.getD (i.1 + 1) 0

def A15OrbitRelation.columnDot
    (profile : A15ProjectorProfile) (relation : A15OrbitRelation)
    (k : Fin profile.orbits.size) : ℚ :=
  relation.multiplier .count +
    ∑ i : Fin 16,
      relation.multiplier (.coordinate i) * profile.orbitAverage k i

def A15OrbitRelation.targetDot
    (profile : A15ProjectorProfile) (relation : A15OrbitRelation) : ℚ :=
  relation.multiplier .count * 220 +
    ∑ i : Fin 16,
      relation.multiplier (.coordinate i) *
        (11 * profile.d.getD i.1 0)

def A15OrbitRelation.check
    (profile : A15ProjectorProfile) (relation : A15OrbitRelation) : Bool :=
  decide (
    relation.coefficients.size = profile.orbits.size ∧
    relation.multipliers.size = 17 ∧
    (∀ k : Fin profile.orbits.size,
      relation.columnDot profile k =
        relation.coefficients.getD k.1 0) ∧
    relation.targetDot profile = relation.constant)

private theorem a15OrbitRelation_sum_expand
    {K I : Type*} [Fintype K] [Fintype I]
    (q0 : ℚ) (q : I → ℚ) (A : I → K → ℚ) (T : K → ℚ) :
    (∑ k, (q0 + ∑ i, q i * A i k) * T k) =
      q0 * ∑ k, T k +
        ∑ i, q i * ∑ k, T k * A i k := by
  calc
    _ = ∑ k, (q0 * T k +
        ∑ i, (q i * A i k) * T k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [add_mul, Finset.sum_mul]
    _ = q0 * ∑ k, T k +
        ∑ k, ∑ i, (q i * A i k) * T k := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = q0 * ∑ k, T k +
        ∑ i, ∑ k, (q i * A i k) * T k := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply congrArg (q0 * ∑ k, T k + ·)
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem A15OrbitRelation.sound
    (profile : A15ProjectorProfile) (relation : A15OrbitRelation)
    (hcheck : relation.check profile = true)
    (totals : Array ℕ) (hvalid : profile.orbitTotalsValid totals) :
    (∑ k : Fin profile.orbits.size,
      (relation.coefficients.getD k.1 0 : ℚ) *
        (totals.getD k.1 0 : ℚ)) =
      relation.constant := by
  have hrelation :
      relation.coefficients.size = profile.orbits.size ∧
      relation.multipliers.size = 17 ∧
      (∀ k : Fin profile.orbits.size,
        relation.columnDot profile k =
          relation.coefficients.getD k.1 0) ∧
      relation.targetDot profile = relation.constant :=
    of_decide_eq_true hcheck
  rcases hvalid with ⟨hsize, hbounds, htotal, hcoordinates⟩
  let T : Fin profile.orbits.size → ℚ :=
    fun k => totals.getD k.1 0
  have htotalQ : (∑ k, T k) = (220 : ℚ) := by
    simpa only [T, Nat.cast_sum, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℚ)) htotal
  have hcoordinateQ (i : Fin 16) :
      (∑ k, T k * profile.orbitAverage k i) =
        11 * profile.d.getD i.1 0 := by
    calc
      _ = ∑ k : Fin profile.orbits.size,
          (totals.getD k.1 0 * profile.orbitFirstMoment k.1 i : ℚ) /
            (profile.orbitSize k.1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [T, A15ProjectorProfile.orbitAverage]
        ring
      _ = _ := hcoordinates i
  calc
    _ = ∑ k : Fin profile.orbits.size,
        relation.columnDot profile k * T k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hrelation.2.2.1 k]
    _ = relation.multiplier .count * ∑ k, T k +
        ∑ i : Fin 16, relation.multiplier (.coordinate i) *
          ∑ k, T k * profile.orbitAverage k i := by
      exact a15OrbitRelation_sum_expand _ _ _ _
    _ = relation.targetDot profile := by
      rw [htotalQ]
      unfold A15OrbitRelation.targetDot
      apply congrArg (relation.multiplier .count * 220 + ·)
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoordinateQ i]
    _ = relation.constant := hrelation.2.2.2

def a15ProjectorArrayVector (x : Array ℤ) : Fin 16 → ℚ :=
  fun i => x.getD i.1 0

def a15ProjectorQForm
    (profile : A15ProjectorProfile) (totals : Array ℕ)
    (x y : Array ℤ) : ℚ :=
  ∑ i : Fin 16, ∑ j : Fin 16,
    (x.getD i.1 0 : ℚ) * profile.projectorEntry totals i j *
      (y.getD j.1 0 : ℚ)

def a15RationalMatrixQForm
    (P : Matrix (Fin 16) (Fin 16) ℚ)
    (x y : Fin 16 → ℚ) : ℚ :=
  ∑ i : Fin 16, ∑ j : Fin 16, x i * P i j * y j

theorem a15RationalMatrixQForm_eq_dotProduct
    (P : Matrix (Fin 16) (Fin 16) ℚ)
    (x y : Fin 16 → ℚ) :
    a15RationalMatrixQForm P x y = x ⬝ᵥ (P *ᵥ y) := by
  simp only [a15RationalMatrixQForm, dotProduct, Matrix.mulVec,
    Finset.mul_sum, mul_assoc]

theorem a15RationalMatrixQForm_add_left
    (P : Matrix (Fin 16) (Fin 16) ℚ)
    (x y z : Fin 16 → ℚ) :
    a15RationalMatrixQForm P (x + y) z =
      a15RationalMatrixQForm P x z +
        a15RationalMatrixQForm P y z := by
  simp [a15RationalMatrixQForm, add_mul, Finset.sum_add_distrib]

theorem a15RationalMatrixQForm_add_right
    (P : Matrix (Fin 16) (Fin 16) ℚ)
    (x y z : Fin 16 → ℚ) :
    a15RationalMatrixQForm P x (y + z) =
      a15RationalMatrixQForm P x y +
        a15RationalMatrixQForm P x z := by
  simp [a15RationalMatrixQForm, mul_add, Finset.sum_add_distrib]

theorem a15RationalMatrixQForm_sub_left
    (P : Matrix (Fin 16) (Fin 16) ℚ)
    (x y z : Fin 16 → ℚ) :
    a15RationalMatrixQForm P (x - y) z =
      a15RationalMatrixQForm P x z -
        a15RationalMatrixQForm P y z := by
  simp [a15RationalMatrixQForm, sub_mul, Finset.sum_sub_distrib]

theorem a15RationalMatrixQForm_sub_right
    (P : Matrix (Fin 16) (Fin 16) ℚ)
    (x y z : Fin 16 → ℚ) :
    a15RationalMatrixQForm P x (y - z) =
      a15RationalMatrixQForm P x y -
        a15RationalMatrixQForm P x z := by
  simp [a15RationalMatrixQForm, mul_sub, Finset.sum_sub_distrib]

theorem a15RationalMatrixQForm_smul_left
    (P : Matrix (Fin 16) (Fin 16) ℚ)
    (c : ℚ) (x y : Fin 16 → ℚ) :
    a15RationalMatrixQForm P (c • x) y =
      c * a15RationalMatrixQForm P x y := by
  unfold a15RationalMatrixQForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp
  ring

theorem a15RationalMatrixQForm_smul_right
    (P : Matrix (Fin 16) (Fin 16) ℚ)
    (c : ℚ) (x y : Fin 16 → ℚ) :
    a15RationalMatrixQForm P x (c • y) =
      c * a15RationalMatrixQForm P x y := by
  unfold a15RationalMatrixQForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp
  ring

theorem a15RationalMatrixQForm_smul_sub_self
    (P : Matrix (Fin 16) (Fin 16) ℚ)
    (c b : ℚ) (x y : Fin 16 → ℚ) :
    a15RationalMatrixQForm P (c • x - b • y) (c • x - b • y) =
      c * c * a15RationalMatrixQForm P x x -
        c * b * a15RationalMatrixQForm P x y -
        b * c * a15RationalMatrixQForm P y x +
        b * b * a15RationalMatrixQForm P y y := by
  rw [a15RationalMatrixQForm_sub_left,
    a15RationalMatrixQForm_sub_right,
    a15RationalMatrixQForm_sub_right]
  simp_rw [a15RationalMatrixQForm_smul_left,
    a15RationalMatrixQForm_smul_right]
  ring

theorem a15RationalMatrixQForm_add_self
    (P : Matrix (Fin 16) (Fin 16) ℚ)
    (x y : Fin 16 → ℚ) :
    a15RationalMatrixQForm P (x + y) (x + y) =
      a15RationalMatrixQForm P x x +
        a15RationalMatrixQForm P x y +
        a15RationalMatrixQForm P y x +
        a15RationalMatrixQForm P y y := by
  rw [a15RationalMatrixQForm_add_left,
    a15RationalMatrixQForm_add_right,
    a15RationalMatrixQForm_add_right]
  ring

theorem a15RationalMatrixQForm_sub_self
    (P : Matrix (Fin 16) (Fin 16) ℚ)
    (x y : Fin 16 → ℚ) :
    a15RationalMatrixQForm P (x - y) (x - y) =
      a15RationalMatrixQForm P x x -
        a15RationalMatrixQForm P x y -
        a15RationalMatrixQForm P y x +
        a15RationalMatrixQForm P y y := by
  rw [a15RationalMatrixQForm_sub_left,
    a15RationalMatrixQForm_sub_right,
    a15RationalMatrixQForm_sub_right]
  ring

theorem a15RationalMatrixQForm_comm_of_posSemidef
    {P : Matrix (Fin 16) (Fin 16) ℚ} (hP : P.PosSemidef)
    (x y : Fin 16 → ℚ) :
    a15RationalMatrixQForm P x y =
      a15RationalMatrixQForm P y x := by
  unfold a15RationalMatrixQForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  have hij : P i j = P j i := by
    simpa using (hP.isHermitian.apply j i)
  rw [hij]
  ring

theorem a15RationalMatrixQForm_self_nonneg
    {P : Matrix (Fin 16) (Fin 16) ℚ} (hP : P.PosSemidef)
    (x : Fin 16 → ℚ) :
    0 ≤ a15RationalMatrixQForm P x x := by
  rw [a15RationalMatrixQForm_eq_dotProduct]
  simpa using hP.dotProduct_mulVec_nonneg x

theorem a15RationalMatrixQForm_minor_nonneg
    {P : Matrix (Fin 16) (Fin 16) ℚ} (hP : P.PosSemidef)
    (x y : Fin 16 → ℚ) :
    0 ≤
      a15RationalMatrixQForm P x x *
          a15RationalMatrixQForm P y y -
        a15RationalMatrixQForm P x y *
          a15RationalMatrixQForm P y x := by
  let a := a15RationalMatrixQForm P x x
  let b := a15RationalMatrixQForm P x y
  let c := a15RationalMatrixQForm P y y
  have hsym : a15RationalMatrixQForm P y x = b := by
    exact a15RationalMatrixQForm_comm_of_posSemidef hP y x
  have ha : 0 ≤ a := a15RationalMatrixQForm_self_nonneg hP x
  have hc : 0 ≤ c := a15RationalMatrixQForm_self_nonneg hP y
  have hfirst :=
    a15RationalMatrixQForm_self_nonneg hP
      (c • x - b • y)
  rw [a15RationalMatrixQForm_smul_sub_self] at hfirst
  have hsecond :=
    a15RationalMatrixQForm_self_nonneg hP
      (b • x - a • y)
  rw [a15RationalMatrixQForm_smul_sub_self] at hsecond
  have hplus :=
    a15RationalMatrixQForm_self_nonneg hP (x + y)
  rw [a15RationalMatrixQForm_add_self] at hplus
  have hminus :=
    a15RationalMatrixQForm_self_nonneg hP (x - y)
  rw [a15RationalMatrixQForm_sub_self] at hminus
  rw [hsym] at hfirst hsecond hplus hminus
  dsimp only [a, b, c] at ha hc hfirst hsecond hplus hminus
  change 0 ≤ a * c -
    a15RationalMatrixQForm P x y *
      a15RationalMatrixQForm P y x
  rw [hsym]
  by_cases hc0 : c = 0
  · by_cases ha0 : a = 0
    · dsimp only [a, b, c] at ha0 hc0 hsym hplus hminus ⊢
      nlinarith
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      dsimp only [a, b, c] at hc0 hsecond ⊢
      nlinarith
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    dsimp only [a, b, c] at hfirst ⊢
    nlinarith

theorem a15ProjectorQForm_eq_rationalMatrixQForm
    (profile : A15ProjectorProfile) (totals : Array ℕ)
    (x y : Array ℤ) :
    a15ProjectorQForm profile totals x y =
      a15RationalMatrixQForm (profile.projectorMatrix totals)
        (a15ProjectorArrayVector x) (a15ProjectorArrayVector y) := by
  rfl

inductive A15ProjectorWitness
  | negativeVector (x : Array ℤ) (reportedValue : ℚ)
  | negativeMinor (x y : Array ℤ) (reportedDeterminant : ℚ)

def A15ProjectorWitness.value
    (profile : A15ProjectorProfile) (totals : Array ℕ) :
    A15ProjectorWitness → ℚ
  | .negativeVector x _ => a15ProjectorQForm profile totals x x
  | .negativeMinor x y _ =>
      a15ProjectorQForm profile totals x x *
          a15ProjectorQForm profile totals y y -
        a15ProjectorQForm profile totals x y *
          a15ProjectorQForm profile totals y x

def A15ProjectorWitness.reportedValue : A15ProjectorWitness → ℚ
  | .negativeVector _ value => value
  | .negativeMinor _ _ value => value

def A15ProjectorWitness.vectorSizesValid : A15ProjectorWitness → Prop
  | .negativeVector x _ => x.size = 16
  | .negativeMinor x y _ => x.size = 16 ∧ y.size = 16

instance (w : A15ProjectorWitness) :
    Decidable w.vectorSizesValid := by
  cases w <;> simp only [A15ProjectorWitness.vectorSizesValid] <;>
    infer_instance

def A15ProjectorWitness.check
    (profile : A15ProjectorProfile) (totals : Array ℕ)
    (witness : A15ProjectorWitness) : Bool :=
  decide (
    witness.vectorSizesValid ∧
    witness.value profile totals = witness.reportedValue ∧
    witness.reportedValue < 0)

theorem A15ProjectorWitness.not_posSemidef
    (profile : A15ProjectorProfile) (totals : Array ℕ)
    (witness : A15ProjectorWitness)
    (hcheck : witness.check profile totals = true) :
    ¬(profile.projectorMatrix totals).PosSemidef := by
  have hw :
      witness.vectorSizesValid ∧
      witness.value profile totals = witness.reportedValue ∧
      witness.reportedValue < 0 :=
    of_decide_eq_true hcheck
  intro hP
  cases witness with
  | negativeVector x reportedValue =>
      have hnonneg :=
        a15RationalMatrixQForm_self_nonneg hP
          (a15ProjectorArrayVector x)
      rw [← a15ProjectorQForm_eq_rationalMatrixQForm] at hnonneg
      simp only [A15ProjectorWitness.value,
        A15ProjectorWitness.reportedValue] at hw
      linarith
  | negativeMinor x y reportedDeterminant =>
      have hnonneg :=
        a15RationalMatrixQForm_minor_nonneg hP
          (a15ProjectorArrayVector x)
          (a15ProjectorArrayVector y)
      rw [← a15ProjectorQForm_eq_rationalMatrixQForm,
        ← a15ProjectorQForm_eq_rationalMatrixQForm,
        ← a15ProjectorQForm_eq_rationalMatrixQForm,
        ← a15ProjectorQForm_eq_rationalMatrixQForm] at hnonneg
      simp only [A15ProjectorWitness.value,
        A15ProjectorWitness.reportedValue] at hw
      linarith

structure A15ProjectorRejection where
  totals : Array ℕ
  witness : A15ProjectorWitness

def A15ProjectorRejection.check
    (profile : A15ProjectorProfile)
    (rejection : A15ProjectorRejection) : Bool :=
  decide (profile.orbitTotalsValid rejection.totals) &&
    rejection.witness.check profile rejection.totals

theorem A15ProjectorRejection.not_posSemidef
    (profile : A15ProjectorProfile)
    (rejection : A15ProjectorRejection)
    (hcheck : rejection.check profile = true) :
    ¬(profile.projectorMatrix rejection.totals).PosSemidef := by
  have hparts :
      decide (profile.orbitTotalsValid rejection.totals) = true ∧
        rejection.witness.check profile rejection.totals = true := by
    simpa only [A15ProjectorRejection.check, Bool.and_eq_true] using hcheck
  exact rejection.witness.not_posSemidef profile rejection.totals hparts.2

structure A15AffineOrbitFormula where
  base : ℤ
  step : ℤ
  relation : A15OrbitRelation
  deriving Inhabited

structure A15OrbitCover where
  parameterized : Bool
  parameterIndex : ℕ
  formulas : Array A15AffineOrbitFormula

def A15OrbitCover.formula
    (cover : A15OrbitCover) (j : ℕ) : A15AffineOrbitFormula :=
  cover.formulas.getD j default

def A15OrbitCover.formulaValue
    (cover : A15OrbitCover) (j z : ℕ) : ℤ :=
  (cover.formula j).base + (cover.formula j).step * z

def A15OrbitCover.candidate
    (profile : A15ProjectorProfile) (cover : A15OrbitCover)
    (z : ℕ) : Array ℕ :=
  Array.ofFn fun j : Fin profile.orbits.size =>
    (cover.formulaValue j.1 z).toNat

def A15OrbitCover.parameterBound
    (profile : A15ProjectorProfile) (cover : A15OrbitCover) : ℕ :=
  if cover.parameterized then
    3 * profile.orbitSize cover.parameterIndex
  else
    0

def A15OrbitCover.parameterAdmissible
    (profile : A15ProjectorProfile) (cover : A15OrbitCover)
    (z : ℕ) : Prop :=
  (∀ j : Fin profile.orbits.size, 0 ≤ cover.formulaValue j.1 z) ∧
    profile.orbitTotalsValid (cover.candidate profile z)

instance (profile : A15ProjectorProfile) (cover : A15OrbitCover)
    (z : ℕ) : Decidable (cover.parameterAdmissible profile z) := by
  unfold A15OrbitCover.parameterAdmissible
  infer_instance

def A15OrbitCover.generatedTotals
    (profile : A15ProjectorProfile) (cover : A15OrbitCover) :
    List (Array ℕ) :=
  ((List.range (cover.parameterBound profile + 1)).filter fun z =>
    cover.parameterAdmissible profile z).map fun z =>
      cover.candidate profile z

def A15OrbitCover.expectedCoefficient
    (cover : A15OrbitCover) (j k : ℕ) : ℤ :=
  (if k = j then 1 else 0) -
    (cover.formula j).step *
      if k = cover.parameterIndex then 1 else 0

def A15OrbitCover.check
    (profile : A15ProjectorProfile) (listedTotals : List (Array ℕ))
    (cover : A15OrbitCover) : Bool :=
  decide (
    cover.parameterIndex < profile.orbits.size ∧
    cover.formulas.size = profile.orbits.size ∧
    (if cover.parameterized then
      (cover.formula cover.parameterIndex).base = 0 ∧
        (cover.formula cover.parameterIndex).step = 1
    else
      ∀ j : Fin profile.orbits.size, (cover.formula j.1).step = 0) ∧
    (∀ j : Fin profile.orbits.size,
      let formula := cover.formula j.1
      formula.relation.check profile = true ∧
      formula.relation.constant = formula.base ∧
      ∀ k : Fin profile.orbits.size,
        formula.relation.coefficients.getD k.1 0 =
          cover.expectedCoefficient j.1 k.1) ∧
    (cover.generatedTotals profile).toFinset = listedTotals.toFinset)

private theorem a15OrbitCover_expected_sum
    (profile : A15ProjectorProfile) (cover : A15OrbitCover)
    (hparameter : cover.parameterIndex < profile.orbits.size)
    (j : Fin profile.orbits.size) (totals : Array ℕ) :
    (∑ k : Fin profile.orbits.size,
      (cover.expectedCoefficient j.1 k.1 : ℚ) *
        (totals.getD k.1 0 : ℚ)) =
      (totals.getD j.1 0 : ℚ) -
        (cover.formula j.1).step *
          (totals.getD cover.parameterIndex 0 : ℚ) := by
  let p : Fin profile.orbits.size :=
    ⟨cover.parameterIndex, hparameter⟩
  simp only [A15OrbitCover.expectedCoefficient, Int.cast_sub,
    Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_mul,
    Finset.sum_sub_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  change
    (∑ k : Fin profile.orbits.size,
      (if k.1 = j.1 then 1 else 0) *
        (totals.getD k.1 0 : ℚ)) -
      (cover.formula j.1).step *
        ∑ k : Fin profile.orbits.size,
          (if k.1 = p.1 then 1 else 0) *
            (totals.getD k.1 0 : ℚ) =
      _
  have hkp (k : Fin profile.orbits.size) :
      (k.1 = cover.parameterIndex) ↔ k = p := by
    simpa only [p] using
      (Fin.ext_iff (a := k) (b := p)).symm
  simp [← Fin.ext_iff, p, hkp]

theorem A15OrbitCover.covers
    (profile : A15ProjectorProfile) (listedTotals : List (Array ℕ))
    (cover : A15OrbitCover)
    (hcheck : cover.check profile listedTotals = true)
    (totals : Array ℕ) (hvalid : profile.orbitTotalsValid totals) :
    totals ∈ listedTotals := by
  have hcover :
      cover.parameterIndex < profile.orbits.size ∧
      cover.formulas.size = profile.orbits.size ∧
      (if cover.parameterized then
        (cover.formula cover.parameterIndex).base = 0 ∧
          (cover.formula cover.parameterIndex).step = 1
      else
        ∀ j : Fin profile.orbits.size, (cover.formula j.1).step = 0) ∧
      (∀ j : Fin profile.orbits.size,
        let formula := cover.formula j.1
        formula.relation.check profile = true ∧
        formula.relation.constant = formula.base ∧
        ∀ k : Fin profile.orbits.size,
          formula.relation.coefficients.getD k.1 0 =
            cover.expectedCoefficient j.1 k.1) ∧
      (cover.generatedTotals profile).toFinset =
        listedTotals.toFinset :=
    of_decide_eq_true hcheck
  rcases hcover with
    ⟨hparameter, hformulaSize, hmode, hrelations, hlisted⟩
  have hformulaZ (j : Fin profile.orbits.size) :
      (totals.getD j.1 0 : ℤ) =
        (cover.formula j.1).base +
          (cover.formula j.1).step *
            (totals.getD cover.parameterIndex 0 : ℤ) := by
    have hrelation := hrelations j
    dsimp only at hrelation
    have hsound :=
      (cover.formula j.1).relation.sound profile hrelation.1
        totals hvalid
    simp_rw [hrelation.2.2] at hsound
    rw [a15OrbitCover_expected_sum profile cover hparameter j totals,
      hrelation.2.1] at hsound
    have hformulaQ :
        (totals.getD j.1 0 : ℚ) =
          (cover.formula j.1).base +
            (cover.formula j.1).step *
              (totals.getD cover.parameterIndex 0 : ℚ) := by
      linarith
    exact_mod_cast hformulaQ
  let z :=
    if cover.parameterized then
      totals.getD cover.parameterIndex 0
    else
      0
  have hvalue (j : Fin profile.orbits.size) :
      (totals.getD j.1 0 : ℤ) = cover.formulaValue j.1 z := by
    by_cases hparameterized : cover.parameterized = true
    · simpa only [z, hparameterized, if_true,
        A15OrbitCover.formulaValue] using hformulaZ j
    · have hnotParameterized :
          cover.parameterized = false :=
        Bool.eq_false_of_not_eq_true hparameterized
      have hsteps :
          ∀ j : Fin profile.orbits.size,
            (cover.formula j.1).step = 0 := by
        simpa only [hnotParameterized, Bool.false_eq_true, if_false] using
          hmode
      simpa only [z, hnotParameterized, Bool.false_eq_true, if_false,
        A15OrbitCover.formulaValue, hsteps j, Int.zero_mul, add_zero] using
        hformulaZ j
  have hcandidate : cover.candidate profile z = totals := by
    apply Array.ext
    · simpa only [A15OrbitCover.candidate, Array.size_ofFn] using
        hvalid.1.symm
    · intro i hicandidate hitotals
      have hi : i < profile.orbits.size := by
        simpa only [A15OrbitCover.candidate, Array.size_ofFn] using
          hicandidate
      let j : Fin profile.orbits.size := ⟨i, hi⟩
      simp only [A15OrbitCover.candidate, Array.getElem_ofFn]
      calc
        (cover.formulaValue i z).toNat =
            ((totals.getD i 0 : ℤ)).toNat := by
          exact congrArg Int.toNat (hvalue j).symm
        _ = totals.getD i 0 := Int.toNat_natCast _
        _ = totals[i] := by
          simp [Array.getD, hitotals]
  have hadmissible : cover.parameterAdmissible profile z := by
    constructor
    · intro j
      rw [← hvalue j]
      omega
    · rw [hcandidate]
      exact hvalid
  have hzle : z ≤ cover.parameterBound profile := by
    by_cases hparameterized : cover.parameterized = true
    · have hbound :=
        hvalid.2.1
          ⟨cover.parameterIndex, hparameter⟩
      simpa only [z, hparameterized, if_true,
        A15OrbitCover.parameterBound] using hbound
    · have hnotParameterized :
          cover.parameterized = false :=
        Bool.eq_false_of_not_eq_true hparameterized
      simp only [z, hnotParameterized, Bool.false_eq_true, if_false,
        A15OrbitCover.parameterBound]
      exact Nat.zero_le 0
  have hgenerated : totals ∈ cover.generatedTotals profile := by
    apply List.mem_map.mpr
    refine ⟨z, ?_, hcandidate⟩
    apply List.mem_filter.mpr
    exact
      ⟨List.mem_range.mpr (Nat.lt_succ_of_le hzle),
        decide_eq_true hadmissible⟩
  have hgeneratedFinset :
      totals ∈ (cover.generatedTotals profile).toFinset :=
    List.mem_toFinset.mpr hgenerated
  rw [hlisted] at hgeneratedFinset
  exact List.mem_toFinset.mp hgeneratedFinset

structure A15ProjectorProfileCertificate where
  profile : A15ProjectorProfile
  rejections : Array A15ProjectorRejection
  survivors : Array (Array ℕ)
  cover : A15OrbitCover

def A15ProjectorProfileCertificate.listedTotals
    (certificate : A15ProjectorProfileCertificate) : List (Array ℕ) :=
  certificate.rejections.toList.map (fun rejection => rejection.totals) ++
    certificate.survivors.toList

def A15ProjectorProfileCertificate.check
    (certificate : A15ProjectorProfileCertificate) : Bool :=
  (certificate.profile.checkOrbitUniverse &&
    certificate.rejections.all
      (A15ProjectorRejection.check certificate.profile)) &&
  (certificate.survivors.all (fun totals =>
      decide (certificate.profile.orbitTotalsValid totals)) &&
    certificate.cover.check certificate.profile certificate.listedTotals)

/-- The three certificate components used by the orbit-total elimination.

The orbit moment tables are connected to the direct shell independently by
`A15ProjectorProfile.bridgeValid`; repeating the full 1,820-subset orbit audit
inside this checker is therefore unnecessary for the downstream argument. -/
def A15ProjectorProfileCertificate.essentialCheck
    (certificate : A15ProjectorProfileCertificate) : Bool :=
  certificate.rejections.all
      (A15ProjectorRejection.check certificate.profile) &&
    (certificate.survivors.all (fun totals =>
      decide (certificate.profile.orbitTotalsValid totals)) &&
    certificate.cover.check certificate.profile certificate.listedTotals)

theorem A15ProjectorProfileCertificate.orbitTotals_complete
    (certificate : A15ProjectorProfileCertificate)
    (hcheck : certificate.essentialCheck = true)
    (totals : Array ℕ)
    (hvalid : certificate.profile.orbitTotalsValid totals) :
    (∃ rejection ∈ certificate.rejections,
      rejection.totals = totals) ∨
      totals ∈ certificate.survivors := by
  have hparts :
      certificate.rejections.all
          (A15ProjectorRejection.check certificate.profile) = true ∧
        (certificate.survivors.all (fun totals =>
        decide (certificate.profile.orbitTotalsValid totals)) = true ∧
      certificate.cover.check certificate.profile
        certificate.listedTotals = true) := by
    simpa only [A15ProjectorProfileCertificate.essentialCheck,
      Bool.and_eq_true] using hcheck
  have hlisted :
      totals ∈ certificate.listedTotals :=
    certificate.cover.covers certificate.profile
      certificate.listedTotals hparts.2.2 totals hvalid
  simp only [A15ProjectorProfileCertificate.listedTotals,
    List.mem_append, List.mem_map] at hlisted
  simpa only [Array.mem_def] using hlisted

theorem A15ProjectorProfileCertificate.rejection_not_posSemidef
    (certificate : A15ProjectorProfileCertificate)
    (hcheck : certificate.essentialCheck = true)
    (rejection : A15ProjectorRejection)
    (hrejection : rejection ∈ certificate.rejections) :
    ¬(certificate.profile.projectorMatrix rejection.totals).PosSemidef := by
  have hparts :
      certificate.rejections.all
          (A15ProjectorRejection.check certificate.profile) = true ∧
        (certificate.survivors.all (fun totals =>
        decide (certificate.profile.orbitTotalsValid totals)) = true ∧
      certificate.cover.check certificate.profile
        certificate.listedTotals = true) := by
    simpa only [A15ProjectorProfileCertificate.essentialCheck,
      Bool.and_eq_true] using hcheck
  have hall :
      ∀ rejection ∈ certificate.rejections,
        rejection.check certificate.profile = true := by
    simpa only [Array.all_eq_true_iff_forall_mem] using hparts.1
  exact rejection.not_posSemidef certificate.profile
    (hall rejection hrejection)

theorem A15ProjectorProfileCertificate.posSemidef_is_survivor
    (certificate : A15ProjectorProfileCertificate)
    (hcheck : certificate.essentialCheck = true)
    (totals : Array ℕ)
    (hvalid : certificate.profile.orbitTotalsValid totals)
    (hposSemidef :
      (certificate.profile.projectorMatrix totals).PosSemidef) :
    totals ∈ certificate.survivors := by
  rcases certificate.orbitTotals_complete hcheck totals hvalid with
    ⟨rejection, hrejection, heq⟩ | hsurvivor
  · have hnot :=
      certificate.rejection_not_posSemidef hcheck rejection hrejection
    rw [heq] at hnot
    exact (hnot hposSemidef).elim
  · exact hsurvivor

end SRG266
