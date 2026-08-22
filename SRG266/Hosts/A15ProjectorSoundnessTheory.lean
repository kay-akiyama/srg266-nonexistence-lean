/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15StandardAverageTheory

/-!
# Generic soundness of A15 averaged-projector witnesses

Most projector witnesses are constant on every coordinate-stabilizer orbit,
so `A15ProjectorBridge` identifies their reported bilinear forms directly
with the positive-semidefinite complement projector of a shell realization.

The remaining witnesses are standard coordinate differences inside one
equal-centroid class.  Their value need not be constant on an orbit.  This
module checks the exact shell difference moment and proves that the reported
quadratic form is the average of direct complement-projector quadratic forms
over all ordered coordinate pairs in that class.  Positivity is therefore
preserved without assuming that the direct shell multiplicities are
stabilizer invariant.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The rational standard coordinate difference `e_i - e_j`. -/
def a15StandardDifferenceVector (i j : Fin 16) : Fin 16 → ℚ :=
  fun l => if l = i then 1 else if l = j then -1 else 0

private def a15StandardBasisVector (i : Fin 16) : Fin 16 → ℚ :=
  fun l => if l = i then 1 else 0

private theorem a15_qform_standardBasis
    (P : Matrix (Fin 16) (Fin 16) ℚ) (i j : Fin 16) :
    a15RationalMatrixQForm P
        (a15StandardBasisVector i)
        (a15StandardBasisVector j) = P i j := by
  simp [a15RationalMatrixQForm, a15StandardBasisVector]

private theorem a15_qform_standardDifference
    (P : Matrix (Fin 16) (Fin 16) ℚ) (i j : Fin 16) (hij : i ≠ j) :
    a15RationalMatrixQForm P
        (a15StandardDifferenceVector i j)
        (a15StandardDifferenceVector i j) =
      P i i - P i j - P j i + P j j := by
  have hvector :
      a15StandardDifferenceVector i j =
        a15StandardBasisVector i - a15StandardBasisVector j := by
    funext l
    simp only [a15StandardDifferenceVector, a15StandardBasisVector,
      Pi.sub_apply]
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
      simp [hli, hlj, hij, Ne.symm hij]
  rw [hvector, a15RationalMatrixQForm_sub_self]
  simp only [a15_qform_standardBasis]

private theorem a15_arrayVector_eq_standardDifference
    (profile : A15ProjectorProfile) (x : Array ℤ)
    (hx : profile.isStandardDifference x) :
    ∃ (c : Fin profile.classSizes.size) (i j : Fin 16),
      profile.inClass c.1 i ∧ profile.inClass c.1 j ∧ i ≠ j ∧
      a15ProjectorArrayVector x = a15StandardDifferenceVector i j := by
  rcases hx with ⟨hxSize, c, i, j, hci, hcj, hij, hx⟩
  refine ⟨c, i, j, hci, hcj, hij, ?_⟩
  funext l
  simp only [a15ProjectorArrayVector, a15StandardDifferenceVector]
  rw [hx l]
  split_ifs <;> norm_num

private theorem A15ProjectorProfile.baseEntry_standardDifference_of_eq
    (profile : A15ProjectorProfile) (i j : Fin 16)
    (hij : i ≠ j)
    (hd : profile.d.getD i.1 0 = profile.d.getD j.1 0) :
    profile.baseEntry i i - profile.baseEntry i j -
        profile.baseEntry j i + profile.baseEntry j j = 2 := by
  unfold A15ProjectorProfile.baseEntry
  simp [hij, Ne.symm hij, hd]
  ring

private theorem A15ProjectorProfile.baseEntry_standardDifference
    (profile : A15ProjectorProfile) (hbridge : profile.bridgeValid)
    (c : Fin profile.classSizes.size) (i j : Fin 16)
    (hci : profile.inClass c.1 i) (hcj : profile.inClass c.1 j)
    (hij : i ≠ j) :
    profile.baseEntry i i - profile.baseEntry i j -
        profile.baseEntry j i + profile.baseEntry j j = 2 := by
  have hdi :
      profile.centroidVector i =
        profile.classValues.getD c.1 0 :=
    (hbridge.2.2.2.2.2.1 c).2.2 i hci
  have hdj :
      profile.centroidVector j =
        profile.classValues.getD c.1 0 :=
    (hbridge.2.2.2.2.2.1 c).2.2 j hcj
  have hd : profile.d.getD i.1 0 = profile.d.getD j.1 0 := by
    exact hdi.trans hdj.symm
  exact profile.baseEntry_standardDifference_of_eq i j hij hd

private theorem A15ProjectorProfile.baseQForm_standardDifference
    (profile : A15ProjectorProfile) (hbridge : profile.bridgeValid)
    (x : Array ℤ) (hx : profile.isStandardDifference x) :
    profile.baseQForm x x = 2 := by
  obtain ⟨c, i, j, hci, hcj, hij, hxVector⟩ :=
    a15_arrayVector_eq_standardDifference profile x hx
  change
    a15RationalMatrixQForm
        (fun i j => profile.baseEntry i j)
        (a15ProjectorArrayVector x)
        (a15ProjectorArrayVector x) = 2
  rw [hxVector, a15_qform_standardDifference _ i j hij]
  exact profile.baseEntry_standardDifference hbridge c i j hci hcj hij

/-- Array representation of `e_i - e_j`, used by the certificate format. -/
def a15StandardDifferenceArray (i j : Fin 16) : Array ℤ :=
  Array.ofFn fun l : Fin 16 =>
    if l = i then 1 else if l = j then -1 else 0

theorem a15StandardDifferenceArray_size (i j : Fin 16) :
    (a15StandardDifferenceArray i j).size = 16 := by
  simp [a15StandardDifferenceArray]

theorem a15StandardDifferenceArray_getD
    (i j l : Fin 16) :
    (a15StandardDifferenceArray i j).getD l.1 0 =
      if l = i then 1 else if l = j then -1 else 0 := by
  simp [a15StandardDifferenceArray, Array.getD, l.isLt]

theorem A15ProjectorProfile.standardDifferenceArray_isStandard
    (profile : A15ProjectorProfile)
    (c : Fin profile.classSizes.size) (i j : Fin 16)
    (hci : profile.inClass c.1 i) (hcj : profile.inClass c.1 j)
    (hij : i ≠ j) :
    profile.isStandardDifference (a15StandardDifferenceArray i j) := by
  refine ⟨a15StandardDifferenceArray_size i j, c, i, j,
    hci, hcj, hij, ?_⟩
  exact a15StandardDifferenceArray_getD i j

private theorem A15ProjectorProfile.shellDot_standardDifference
    (profile : A15ProjectorProfile)
    (s : A15EligibleIndex profile.centroidVector)
    (i j : Fin 16) (hij : i ≠ j) :
    profile.shellDot (a15StandardDifferenceArray i j) s =
      a15ProjectorShellCoordinate profile.d
          (a15FourSubsetAt s.1) i -
        a15ProjectorShellCoordinate profile.d
          (a15FourSubsetAt s.1) j := by
  change
    (∑ l : Fin 16,
      (a15StandardDifferenceArray i j).getD l.1 0 *
        a15ProjectorShellCoordinate profile.d
          (a15FourSubsetAt s.1) l) = _
  simp_rw [a15StandardDifferenceArray_getD i j]
  simp only [ite_mul, one_mul, neg_mul, zero_mul]
  calc
    (∑ l : Fin 16,
      (if l = i then
        a15ProjectorShellCoordinate profile.d (a15FourSubsetAt s.1) l
      else if l = j then
        -a15ProjectorShellCoordinate profile.d (a15FourSubsetAt s.1) l
      else 0)) =
        ∑ l : Fin 16,
          ((if l = i then
              a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) l
            else 0) -
            (if l = j then
              a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) l
            else 0)) := by
      apply Finset.sum_congr rfl
      intro l _
      by_cases hli : l = i <;> by_cases hlj : l = j <;>
        simp [hli, hlj, hij, Ne.symm hij]
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Direct complement-projector form of one coordinate difference whose two
centroid coordinates agree.  No generated orbit moments are needed. -/
theorem A15ShellGramRealization.directQForm_standardDifference_of_eq
    {x : V} (profile : A15ProjectorProfile)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (i j : Fin 16) (hij : i ≠ j)
    (hd : profile.d.getD i.1 0 = profile.d.getD j.1 0) :
    a15RationalMatrixQForm (realization.complementProjector G)
        (a15StandardDifferenceVector i j)
        (a15StandardDifferenceVector i j) =
      2 -
        (∑ s : A15EligibleIndex profile.centroidVector,
          ((realization.toFiniteShell G).multiplicity G s : ℚ) *
            (a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) i -
              a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) j) ^ 2) / 720 := by
  let a := a15StandardDifferenceArray i j
  have haVector :
      a15ProjectorArrayVector a =
        a15StandardDifferenceVector i j := by
    funext l
    simp only [a, a15ProjectorArrayVector,
      a15StandardDifferenceVector]
    rw [a15StandardDifferenceArray_getD]
    split_ifs <;> norm_num
  rw [← haVector, a15DirectQForm_expand]
  have hbase : profile.baseQForm a a = 2 := by
    change
      a15RationalMatrixQForm
          (fun i j => profile.baseEntry i j)
          (a15ProjectorArrayVector a)
          (a15ProjectorArrayVector a) = 2
    rw [haVector, a15_qform_standardDifference _ i j hij]
    exact profile.baseEntry_standardDifference_of_eq i j hij hd
  rw [hbase]
  apply congrArg (2 - ·)
  apply congrArg (· / 720)
  apply Finset.sum_congr rfl
  intro s _
  rw [profile.shellDot_standardDifference s i j hij]
  push_cast
  ring

/-- Direct complement-projector form of one standard coordinate difference. -/
theorem A15ShellGramRealization.directQForm_standardDifference
    {x : V} (profile : A15ProjectorProfile)
    (hbridge : profile.bridgeValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (c : Fin profile.classSizes.size) (i j : Fin 16)
    (hci : profile.inClass c.1 i) (hcj : profile.inClass c.1 j)
    (hij : i ≠ j) :
    a15RationalMatrixQForm (realization.complementProjector G)
        (a15StandardDifferenceVector i j)
        (a15StandardDifferenceVector i j) =
      2 -
        (∑ s : A15EligibleIndex profile.centroidVector,
          ((realization.toFiniteShell G).multiplicity G s : ℚ) *
        (a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) i -
              a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) j) ^ 2) / 720 := by
  have hdi :
      profile.centroidVector i =
        profile.classValues.getD c.1 0 :=
    (hbridge.2.2.2.2.2.1 c).2.2 i hci
  have hdj :
      profile.centroidVector j =
        profile.classValues.getD c.1 0 :=
    (hbridge.2.2.2.2.2.1 c).2.2 j hcj
  exact realization.directQForm_standardDifference_of_eq G profile i j hij
    (hdi.trans hdj.symm)

/-- Sum of direct quadratic forms over ordered distinct pairs in a centroid
coordinate class. -/
noncomputable def A15ShellGramRealization.standardDifferenceQSum
    {x : V} (profile : A15ProjectorProfile)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (c : ℕ) : ℚ :=
  ∑ i ∈ profile.classFinset c,
    ∑ j ∈ (profile.classFinset c).erase i,
      a15RationalMatrixQForm (realization.complementProjector G)
        (a15StandardDifferenceVector i j)
        (a15StandardDifferenceVector i j)

/-- The direct ordered-pair sum is nonnegative when the centroid lies in the
sum-zero hyperplane. -/
theorem A15ShellGramRealization.standardDifferenceQSum_nonneg_of_sum_zero
    (hG : IsHypothetical G) (x : V)
    (profile : A15ProjectorProfile)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (hdSum : ∑ i, profile.centroidVector i = 0)
    (c : ℕ) :
    0 ≤ realization.standardDifferenceQSum G profile c := by
  unfold A15ShellGramRealization.standardDifferenceQSum
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact
    a15RationalMatrixQForm_self_nonneg
      (realization.complementProjector_posSemidef
        G hG x hdSum)
      (a15StandardDifferenceVector i j)

/-- The direct ordered-pair sum is nonnegative because every summand is a
quadratic form of the positive-semidefinite complement projector. -/
theorem A15ShellGramRealization.standardDifferenceQSum_nonneg
    (hG : IsHypothetical G) (x : V)
    (profile : A15ProjectorProfile) (hbridge : profile.bridgeValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (c : ℕ) :
    0 ≤ realization.standardDifferenceQSum G profile c :=
  realization.standardDifferenceQSum_nonneg_of_sum_zero
    G hG x profile hbridge.2.2.2.2.1 c

private theorem A15ProjectorProfile.orbitSecondBilinear_standardDifference
    (profile : A15ProjectorProfile) (k : ℕ)
    (i j : Fin 16) (hij : i ≠ j) :
    (profile.orbitSecondBilinear k
        (a15StandardDifferenceArray i j)
        (a15StandardDifferenceArray i j) : ℚ) =
      (profile.orbitSecondMoment k i i : ℚ) -
        profile.orbitSecondMoment k i j -
        profile.orbitSecondMoment k j i +
        profile.orbitSecondMoment k j j := by
  have hvector :
      a15ProjectorArrayVector (a15StandardDifferenceArray i j) =
        a15StandardDifferenceVector i j := by
    funext l
    simp only [a15ProjectorArrayVector, a15StandardDifferenceVector]
    rw [a15StandardDifferenceArray_getD]
    split_ifs <;> norm_num
  calc
    (profile.orbitSecondBilinear k
        (a15StandardDifferenceArray i j)
        (a15StandardDifferenceArray i j) : ℚ) =
        a15RationalMatrixQForm
          (fun i j => (profile.orbitSecondMoment k i j : ℚ))
          (a15ProjectorArrayVector (a15StandardDifferenceArray i j))
          (a15ProjectorArrayVector
            (a15StandardDifferenceArray i j)) := by
      unfold A15ProjectorProfile.orbitSecondBilinear
      push_cast
      rfl
    _ = _ := by
      rw [hvector, a15_qform_standardDifference _ i j hij]

/-- The checked standard-moment equation, normalized as a rational orbit
average. -/
private theorem A15ProjectorProfile.standardDifference_orbitAverage
    (profile : A15ProjectorProfile) (hbridge : profile.bridgeValid)
    (c : Fin profile.classSizes.size) (i j : Fin 16)
    (hci : profile.inClass c.1 i) (hcj : profile.inClass c.1 j)
    (hij : i ≠ j) (k : Fin profile.orbits.size) :
    (profile.classSizes.getD c.1 0 : ℚ) *
        ((profile.classSizes.getD c.1 0 : ℚ) - 1) *
          (profile.orbitSecondBilinear k.1
            (a15StandardDifferenceArray i j)
            (a15StandardDifferenceArray i j) : ℚ) /
        (profile.orbitSize k.1 : ℚ) =
      32 * (profile.orbitClassCount k.1 c.1 : ℚ) *
        ((profile.classSizes.getD c.1 0 : ℚ) -
          profile.orbitClassCount k.1 c.1) := by
  have horbit := hbridge.2.2.2.2.2.2.2.2 k
  have hsize : (profile.orbitSize k.1 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt horbit.1
  have hmoment :=
    horbit.2.2.2.2.2 c i j hci hcj hij
  unfold A15ProjectorProfile.standardMomentEquation at hmoment
  have hmomentQ :
      (((profile.classSizes.getD c.1 0 : ℚ) *
          ((profile.classSizes.getD c.1 0 : ℚ) - 1)) *
        ((profile.orbitSecondMoment k.1 i i : ℚ) -
          profile.orbitSecondMoment k.1 i j -
          profile.orbitSecondMoment k.1 j i +
          profile.orbitSecondMoment k.1 j j)) =
        (profile.orbitSize k.1 : ℚ) *
          (32 * (profile.orbitClassCount k.1 c.1 : ℚ) *
            ((profile.classSizes.getD c.1 0 : ℚ) -
              profile.orbitClassCount k.1 c.1)) := by
    exact_mod_cast hmoment
  rw [profile.orbitSecondBilinear_standardDifference k.1 i j hij]
  field_simp
  nlinarith

/-- The averaged certificate form of a standard difference, after clearing
the number of ordered coordinate pairs. -/
theorem A15ProjectorProfile.projectorQForm_standardDifference_scaled
    (profile : A15ProjectorProfile) (hbridge : profile.bridgeValid)
    (totals : Array ℕ)
    (c : Fin profile.classSizes.size) (i j : Fin 16)
    (hci : profile.inClass c.1 i) (hcj : profile.inClass c.1 j)
    (hij : i ≠ j) :
    (profile.classSizes.getD c.1 0 : ℚ) *
        ((profile.classSizes.getD c.1 0 : ℚ) - 1) *
      a15ProjectorQForm profile totals
        (a15StandardDifferenceArray i j)
        (a15StandardDifferenceArray i j) =
      2 * ((profile.classSizes.getD c.1 0 : ℚ) *
          ((profile.classSizes.getD c.1 0 : ℚ) - 1)) -
        (∑ k : Fin profile.orbits.size,
          (totals.getD k.1 0 : ℚ) *
            (32 * (profile.orbitClassCount k.1 c.1 : ℚ) *
              ((profile.classSizes.getD c.1 0 : ℚ) -
                profile.orbitClassCount k.1 c.1))) / 720 := by
  let a := a15StandardDifferenceArray i j
  have ha :
      profile.isStandardDifference a :=
    profile.standardDifferenceArray_isStandard c i j hci hcj hij
  rw [a15ProjectorQForm_expand,
    profile.baseQForm_standardDifference hbridge a ha]
  let N : ℚ :=
    (profile.classSizes.getD c.1 0 : ℚ) *
      ((profile.classSizes.getD c.1 0 : ℚ) - 1)
  calc
    (profile.classSizes.getD c.1 0 : ℚ) *
        ((profile.classSizes.getD c.1 0 : ℚ) - 1) *
        (2 -
          (∑ k : Fin profile.orbits.size,
            (totals.getD k.1 0 : ℚ) *
              profile.orbitSecondBilinear k.1 a a /
                (profile.orbitSize k.1 : ℚ)) / 720) =
      2 * N -
        (∑ k : Fin profile.orbits.size,
          (totals.getD k.1 0 : ℚ) *
            (N *
              profile.orbitSecondBilinear k.1 a a /
                (profile.orbitSize k.1 : ℚ))) / 720 := by
      change N * (2 - _) = _
      calc
        N * (2 -
            (∑ k : Fin profile.orbits.size,
              (totals.getD k.1 0 : ℚ) *
                profile.orbitSecondBilinear k.1 a a /
                  (profile.orbitSize k.1 : ℚ)) / 720) =
            2 * N -
              (N * (∑ k : Fin profile.orbits.size,
                (totals.getD k.1 0 : ℚ) *
                  profile.orbitSecondBilinear k.1 a a /
                    (profile.orbitSize k.1 : ℚ))) / 720 := by
          ring
        _ = _ := by
          apply congrArg (2 * N - ·)
          apply congrArg (· / 720)
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = _ := by
      apply congrArg (2 * N - ·)
      apply congrArg (· / 720)
      apply Finset.sum_congr rfl
      intro k _
      rw [profile.standardDifference_orbitAverage
        hbridge c i j hci hcj hij k]

/-- Regroup the direct shell difference moments by the checked orbit
partition. -/
theorem A15ShellGramRealization.shellDifferenceMoment_regroup
    {x : V} (profile : A15ProjectorProfile)
    (hbridge : profile.bridgeValid)
    (hstandard : profile.standardAverageValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (c : Fin profile.classSizes.size) :
    (∑ s : A15EligibleIndex profile.centroidVector,
      ((realization.toFiniteShell G).multiplicity G s : ℚ) *
        (profile.shellDifferenceMoment c.1 s : ℚ)) =
      ∑ k : Fin profile.orbits.size,
        ((realization.projectorOrbitTotals G profile).getD k.1 0 : ℚ) *
          (32 * (profile.orbitClassCount k.1 c.1 : ℚ) *
            ((profile.classSizes.getD c.1 0 : ℚ) -
              profile.orbitClassCount k.1 c.1)) := by
  let finite := realization.toFiniteShell G
  have hunique := hbridge.2.2.2.2.2.2.2.1
  have hget (k : Fin profile.orbits.size) :
      (realization.projectorOrbitTotals G profile).getD k.1 0 =
        ∑ s ∈ profile.orbitIndexFinset k.1,
          finite.multiplicity G s := by
    simp [A15ShellGramRealization.projectorOrbitTotals, finite, k.isLt]
  symm
  simp_rw [hget]
  calc
    (∑ k : Fin profile.orbits.size,
      ((∑ s ∈ profile.orbitIndexFinset k.1,
          finite.multiplicity G s : ℕ) : ℚ) *
        (32 * (profile.orbitClassCount k.1 c.1 : ℚ) *
          ((profile.classSizes.getD c.1 0 : ℚ) -
            profile.orbitClassCount k.1 c.1))) =
        ∑ k : Fin profile.orbits.size,
          ∑ s ∈ profile.orbitIndexFinset k.1,
            (finite.multiplicity G s : ℚ) *
              (32 * (profile.orbitClassCount k.1 c.1 : ℚ) *
                ((profile.classSizes.getD c.1 0 : ℚ) -
                  profile.orbitClassCount k.1 c.1)) := by
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      rw [Finset.sum_mul]
    _ = ∑ s : A15EligibleIndex profile.centroidVector,
        ∑ k : Fin profile.orbits.size,
          if profile.indexMatches k.1 s.1 then
            (finite.multiplicity G s : ℚ) *
              (32 * (profile.orbitClassCount k.1 c.1 : ℚ) *
                ((profile.classSizes.getD c.1 0 : ℚ) -
                  profile.orbitClassCount k.1 c.1))
          else 0 := by
      simp only [A15ProjectorProfile.orbitIndexFinset,
        Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ s : A15EligibleIndex profile.centroidVector,
        (finite.multiplicity G s : ℚ) *
          (profile.shellDifferenceMoment c.1 s : ℚ) := by
      apply Finset.sum_congr rfl
      intro s _
      apply a15_sum_unique_index_match_rat profile hunique s
      intro k hmatch
      have hmoment := hstandard k c s hmatch
      rw [hmoment]
      push_cast
      ring
    _ = _ := by
      rfl

/-- The direct ordered-pair sum is the constant pair contribution minus the
corresponding shell-difference moment.  This identity needs no orbit moment
table. -/
theorem A15ShellGramRealization.standardDifferenceQSum_eq_shellMoment
    {x : V} (profile : A15ProjectorProfile)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (c : Fin profile.classSizes.size)
    (hnpos : 0 < profile.classSizes.getD c.1 0)
    (hcard : (profile.classFinset c.1).card =
      profile.classSizes.getD c.1 0)
    (hclass : ∀ i, profile.inClass c.1 i →
      profile.centroidVector i = profile.classValues.getD c.1 0) :
    realization.standardDifferenceQSum G profile c.1 =
      2 * ((profile.classSizes.getD c.1 0 : ℚ) *
        ((profile.classSizes.getD c.1 0 : ℚ) - 1)) -
      (∑ s : A15EligibleIndex profile.centroidVector,
        ((realization.toFiniteShell G).multiplicity G s : ℚ) *
          (profile.shellDifferenceMoment c.1 s : ℚ)) / 720 := by
  let C := profile.classFinset c.1
  let n := profile.classSizes.getD c.1 0
  have hcard' : C.card = n := hcard
  have hnpos' : 0 < n := hnpos
  have hpairCount :
      (∑ i ∈ C, (C.erase i).card) = n * (n - 1) := by
    calc
      (∑ i ∈ C, (C.erase i).card) =
          ∑ i ∈ C, (n - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.card_erase_of_mem hi, hcard']
      _ = C.card * (n - 1) := by
        simp
      _ = n * (n - 1) := by
        rw [hcard']
  have hpairConstant :
      (∑ i ∈ C, ∑ _j ∈ C.erase i, (2 : ℚ)) =
        2 * ((n : ℚ) * ((n : ℚ) - 1)) := by
    calc
      (∑ i ∈ C, ∑ _j ∈ C.erase i, (2 : ℚ)) =
          ((∑ i ∈ C, (C.erase i).card : ℕ) : ℚ) * 2 := by
        push_cast
        simp [Finset.sum_mul]
      _ = ((n * (n - 1) : ℕ) : ℚ) * 2 := by
        rw [hpairCount]
      _ = 2 * ((n : ℚ) * ((n : ℚ) - 1)) := by
        rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt hnpos'))]
        norm_num
        ring
  have hshell :
      (∑ i ∈ C, ∑ j ∈ C.erase i,
        ∑ s : A15EligibleIndex profile.centroidVector,
          ((realization.toFiniteShell G).multiplicity G s : ℚ) *
            (a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) i -
              a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) j) ^ 2) =
        ∑ s : A15EligibleIndex profile.centroidVector,
          ((realization.toFiniteShell G).multiplicity G s : ℚ) *
            (profile.shellDifferenceMoment c.1 s : ℚ) := by
    calc
      (∑ i ∈ C, ∑ j ∈ C.erase i,
        ∑ s : A15EligibleIndex profile.centroidVector,
          ((realization.toFiniteShell G).multiplicity G s : ℚ) *
            (a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) i -
              a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) j) ^ 2) =
          ∑ i ∈ C,
            ∑ s : A15EligibleIndex profile.centroidVector,
              ∑ j ∈ C.erase i,
                ((realization.toFiniteShell G).multiplicity G s : ℚ) *
                  (a15ProjectorShellCoordinate profile.d
                      (a15FourSubsetAt s.1) i -
                    a15ProjectorShellCoordinate profile.d
                      (a15FourSubsetAt s.1) j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ s : A15EligibleIndex profile.centroidVector,
            ∑ i ∈ C, ∑ j ∈ C.erase i,
              ((realization.toFiniteShell G).multiplicity G s : ℚ) *
                (a15ProjectorShellCoordinate profile.d
                    (a15FourSubsetAt s.1) i -
                  a15ProjectorShellCoordinate profile.d
                    (a15FourSubsetAt s.1) j) ^ 2 := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s _
        unfold A15ProjectorProfile.shellDifferenceMoment
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
  unfold A15ShellGramRealization.standardDifferenceQSum
  calc
    (∑ i ∈ profile.classFinset c.1,
      ∑ j ∈ (profile.classFinset c.1).erase i,
        a15RationalMatrixQForm (realization.complementProjector G)
          (a15StandardDifferenceVector i j)
          (a15StandardDifferenceVector i j)) =
        ∑ i ∈ C, ∑ j ∈ C.erase i,
          (2 -
            (∑ s : A15EligibleIndex profile.centroidVector,
              ((realization.toFiniteShell G).multiplicity G s : ℚ) *
                (a15ProjectorShellCoordinate profile.d
                    (a15FourSubsetAt s.1) i -
                  a15ProjectorShellCoordinate profile.d
                    (a15FourSubsetAt s.1) j) ^ 2) / 720) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hjC : j ∈ C := Finset.mem_of_mem_erase hj
      have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
      have hci : profile.inClass c.1 i :=
        (Finset.mem_filter.mp hi).2
      have hcj : profile.inClass c.1 j :=
        (Finset.mem_filter.mp hjC).2
      exact realization.directQForm_standardDifference_of_eq G profile i j
        hij ((hclass i hci).trans (hclass j hcj).symm)
    _ = 2 * ((n : ℚ) * ((n : ℚ) - 1)) -
        (∑ s : A15EligibleIndex profile.centroidVector,
          ((realization.toFiniteShell G).multiplicity G s : ℚ) *
            (profile.shellDifferenceMoment c.1 s : ℚ)) / 720 := by
      simp_rw [Finset.sum_sub_distrib]
      rw [hpairConstant]
      apply congrArg
        (2 * ((n : ℚ) * ((n : ℚ) - 1)) - ·)
      calc
        (∑ i ∈ C, ∑ j ∈ C.erase i,
          (∑ s : A15EligibleIndex profile.centroidVector,
            ((realization.toFiniteShell G).multiplicity G s : ℚ) *
              (a15ProjectorShellCoordinate profile.d
                  (a15FourSubsetAt s.1) i -
                a15ProjectorShellCoordinate profile.d
                  (a15FourSubsetAt s.1) j) ^ 2) / 720) =
            ∑ i ∈ C,
              (∑ j ∈ C.erase i,
                ∑ s : A15EligibleIndex profile.centroidVector,
                  ((realization.toFiniteShell G).multiplicity G s : ℚ) *
                    (a15ProjectorShellCoordinate profile.d
                        (a15FourSubsetAt s.1) i -
                      a15ProjectorShellCoordinate profile.d
                        (a15FourSubsetAt s.1) j) ^ 2) / 720 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_div]
        _ = (∑ i ∈ C, ∑ j ∈ C.erase i,
              ∑ s : A15EligibleIndex profile.centroidVector,
                ((realization.toFiniteShell G).multiplicity G s : ℚ) *
                  (a15ProjectorShellCoordinate profile.d
                      (a15FourSubsetAt s.1) i -
                    a15ProjectorShellCoordinate profile.d
                      (a15FourSubsetAt s.1) j) ^ 2) / 720 := by
          rw [Finset.sum_div]
        _ = _ := by
          rw [hshell]

/-- The direct ordered-pair sum has the same cleared expression as the
averaged certificate form. -/
theorem A15ShellGramRealization.standardDifferenceQSum_eq_orbitExpression
    {x : V} (profile : A15ProjectorProfile)
    (hbridge : profile.bridgeValid)
    (hstandard : profile.standardAverageValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (c : Fin profile.classSizes.size) :
    realization.standardDifferenceQSum G profile c.1 =
      2 * ((profile.classSizes.getD c.1 0 : ℚ) *
        ((profile.classSizes.getD c.1 0 : ℚ) - 1)) -
      (∑ k : Fin profile.orbits.size,
        ((realization.projectorOrbitTotals G profile).getD k.1 0 : ℚ) *
          (32 * (profile.orbitClassCount k.1 c.1 : ℚ) *
            ((profile.classSizes.getD c.1 0 : ℚ) -
              profile.orbitClassCount k.1 c.1))) / 720 := by
  rw [realization.standardDifferenceQSum_eq_shellMoment G profile c
    (hbridge.2.2.2.2.2.1 c).1
    (hbridge.2.2.2.2.2.1 c).2.1
    (hbridge.2.2.2.2.2.1 c).2.2]
  rw [realization.shellDifferenceMoment_regroup
    G profile hbridge hstandard c]

/-- Every checked standard-difference quadratic form is nonnegative for orbit
totals coming from a direct shell realization. -/
theorem A15ShellGramRealization.projectorQForm_standardDifference_nonneg
    (hG : IsHypothetical G) (x : V)
    (profile : A15ProjectorProfile)
    (hbridge : profile.bridgeValid)
    (hstandard : profile.standardAverageValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (a : Array ℤ) (ha : profile.isStandardDifference a) :
    0 ≤ a15ProjectorQForm profile
      (realization.projectorOrbitTotals G profile) a a := by
  obtain ⟨c, i, j, hci, hcj, hij, haVector⟩ :=
    a15_arrayVector_eq_standardDifference profile a ha
  have hiC : i ∈ profile.classFinset c.1 := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hci⟩
  have hjC : j ∈ profile.classFinset c.1 := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hcj⟩
  have hclassLarge :
      1 < (profile.classFinset c.1).card :=
    Finset.one_lt_card_iff.mpr ⟨i, j, hiC, hjC, hij⟩
  have hnLarge :
      1 < profile.classSizes.getD c.1 0 := by
    rw [← (hbridge.2.2.2.2.2.1 c).2.1]
    exact hclassLarge
  have hNpos :
      0 < (profile.classSizes.getD c.1 0 : ℚ) *
        ((profile.classSizes.getD c.1 0 : ℚ) - 1) := by
    have hnLargeQ :
        (1 : ℚ) < profile.classSizes.getD c.1 0 := by
      exact_mod_cast hnLarge
    exact mul_pos (lt_trans zero_lt_one hnLargeQ) (sub_pos.mpr hnLargeQ)
  let a₀ := a15StandardDifferenceArray i j
  have ha₀Vector :
      a15ProjectorArrayVector a₀ =
        a15StandardDifferenceVector i j := by
    funext l
    simp only [a₀, a15ProjectorArrayVector,
      a15StandardDifferenceVector]
    rw [a15StandardDifferenceArray_getD]
    split_ifs <;> norm_num
  have hform :
      a15ProjectorQForm profile
          (realization.projectorOrbitTotals G profile) a a =
        a15ProjectorQForm profile
          (realization.projectorOrbitTotals G profile) a₀ a₀ := by
    rw [a15ProjectorQForm_eq_rationalMatrixQForm,
      a15ProjectorQForm_eq_rationalMatrixQForm,
      haVector, ha₀Vector]
  have hscaled :=
    profile.projectorQForm_standardDifference_scaled hbridge
      (realization.projectorOrbitTotals G profile)
      c i j hci hcj hij
  have hsumEq :=
    realization.standardDifferenceQSum_eq_orbitExpression
      G profile hbridge hstandard c
  have hsumNonneg :=
    realization.standardDifferenceQSum_nonneg
      G hG x profile hbridge c.1
  have hscaledEq :
      (profile.classSizes.getD c.1 0 : ℚ) *
          ((profile.classSizes.getD c.1 0 : ℚ) - 1) *
        a15ProjectorQForm profile
          (realization.projectorOrbitTotals G profile) a₀ a₀ =
        realization.standardDifferenceQSum G profile c.1 := by
    linarith
  rw [hform]
  nlinarith

/-- Every supported rejection witness has nonnegative value on orbit totals
coming from a direct shell realization. -/
theorem A15ProjectorWitness.value_nonneg_of_realization
    (hG : IsHypothetical G) (x : V)
    (profile : A15ProjectorProfile)
    (hbridge : profile.bridgeValid)
    (hstandard : profile.standardAverageValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (witness : A15ProjectorWitness)
    (hcompatible : witness.bridgeCompatible profile) :
    0 ≤ witness.value profile
      (realization.projectorOrbitTotals G profile) := by
  cases witness with
  | negativeVector a reportedValue =>
      simp only [A15ProjectorWitness.value]
      rcases hcompatible with hbilinear | hstandardDifference
      · rw [realization.projectorQForm_eq_direct
          G profile hbridge a a hbilinear]
        exact
          a15RationalMatrixQForm_self_nonneg
            (realization.complementProjector_posSemidef
              G hG x hbridge.2.2.2.2.1)
            (a15ProjectorArrayVector a)
      · exact
          realization.projectorQForm_standardDifference_nonneg
            G hG x profile hbridge hstandard a hstandardDifference
  | negativeMinor a b reportedDeterminant =>
      rcases hcompatible with ⟨haa, hab, hba, hbb⟩
      simp only [A15ProjectorWitness.value]
      rw [realization.projectorQForm_eq_direct
          G profile hbridge a a haa,
        realization.projectorQForm_eq_direct
          G profile hbridge a b hab,
        realization.projectorQForm_eq_direct
          G profile hbridge b a hba,
        realization.projectorQForm_eq_direct
          G profile hbridge b b hbb]
      exact
        a15RationalMatrixQForm_minor_nonneg
          (realization.complementProjector_posSemidef
            G hG x hbridge.2.2.2.2.1)
          (a15ProjectorArrayVector a)
          (a15ProjectorArrayVector b)

/-- A checked negative rejection cannot be the orbit-total vector of a direct
shell realization. -/
theorem A15ProjectorRejection.ne_projectorOrbitTotals
    (hG : IsHypothetical G) (x : V)
    (profile : A15ProjectorProfile)
    (hbridge : profile.bridgeValid)
    (hstandard : profile.standardAverageValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (rejection : A15ProjectorRejection)
    (hcheck : rejection.check profile = true)
    (hcompatible : rejection.witness.bridgeCompatible profile) :
    rejection.totals ≠
      realization.projectorOrbitTotals G profile := by
  intro heq
  have hparts :
      decide (profile.orbitTotalsValid rejection.totals) = true ∧
        rejection.witness.check profile rejection.totals = true := by
    simpa only [A15ProjectorRejection.check, Bool.and_eq_true] using hcheck
  have hw :
      rejection.witness.vectorSizesValid ∧
        rejection.witness.value profile rejection.totals =
          rejection.witness.reportedValue ∧
        rejection.witness.reportedValue < 0 :=
    of_decide_eq_true hparts.2
  have hnonneg :=
    rejection.witness.value_nonneg_of_realization
      G hG x profile hbridge hstandard realization hcompatible
  rw [← heq] at hnonneg
  linarith

/-- A single audited certificate transports direct shell multiplicities to
its survivor array.  The global thirteen-profile theorem is only one caller
of this profile-local interface. -/
theorem A15ShellGramRealization.projectorOrbitTotals_mem_survivors_of
    (hG : IsHypothetical G) (x : V)
    (certificate : A15ProjectorProfileCertificate)
    (hcheck : certificate.essentialCheck = true)
    (hbridge : certificate.profile.bridgeValid)
    (hcompatible : ∀ rejection ∈ certificate.rejections,
      rejection.witness.bridgeCompatible certificate.profile)
    (realization :
      A15ShellGramRealization G x certificate.profile.centroidVector) :
    realization.projectorOrbitTotals G certificate.profile ∈
      certificate.survivors := by
  have hstandard : certificate.profile.standardAverageValid :=
    certificate.profile.standardAverageValid_of_bridgeValid hbridge
  have hvalid :=
    realization.projectorOrbitTotals_valid
      G hG x certificate.profile hbridge
  rcases certificate.orbitTotals_complete hcheck
      (realization.projectorOrbitTotals G certificate.profile)
      hvalid with
    ⟨rejection, hrejection, heq⟩ | hsurvivor
  · have hrejectCheck :
        rejection.check certificate.profile = true := by
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
      exact hall rejection hrejection
    exact
      (rejection.ne_projectorOrbitTotals G hG x certificate.profile
        hbridge hstandard realization hrejectCheck
        (hcompatible rejection hrejection) heq).elim
  · exact hsurvivor

end SRG266
