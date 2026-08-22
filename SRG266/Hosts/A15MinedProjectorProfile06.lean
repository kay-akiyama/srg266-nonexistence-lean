/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15MinedProjectorTheory
import SRG266.Hosts.A15MinedNormProfileData
import SRG266.Hosts.A15MinedSearch

/-!
# Mined exclusion of A15 projector profile 6

The certificate rejects 111 orbit-total candidates.  They all share a
single obstruction: the indicator of the six-coordinate `-10` class has
complement-projector quadratic value `-13/36`.

For every eligible shell vector, if `z₀` and `z₁` are its sums over the
`-30` and `-10` coordinate classes, then

`z₁² = -28 - 8 z₀ - 8 z₁`.

The centroid equations therefore force the total square sum to be `4400`.
This proof uses no orbit table, membership audit, or rejection list.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The class-only skeleton of generated projector profile 6. -/
def a15MinedProjectorProfile06 : A15ProjectorProfile where
  centroidIndex := 6
  d := #[-30, -30,
    -10, -10, -10, -10, -10, -10,
    10, 10, 10, 10, 10, 10,
    30, 30]
  reportedEligible := 152
  classValues := #[-30, -10, 10, 30]
  classSizes := #[2, 6, 6, 2]
  orbits := #[]

theorem a15MinedProjectorProfile06_centroidVector :
    a15MinedProjectorProfile06.centroidVector =
      a15SmallProfile a15MinedNormProfile08 := by
  funext i
  fin_cases i <;> rfl

private theorem a15MinedProjectorProfile06_static :
    (∑ i, a15MinedProjectorProfile06.centroidVector i) = 0 ∧
    (∀ i, a15MinedProjectorProfile06.classIndexCount i = 1) ∧
    (∀ c : Fin a15MinedProjectorProfile06.classSizes.size,
      (a15MinedProjectorProfile06.classFinset c.1).card =
        a15MinedProjectorProfile06.classSizes.getD c.1 0 ∧
      ∀ i, a15MinedProjectorProfile06.inClass c.1 i →
        a15MinedProjectorProfile06.centroidVector i =
          a15MinedProjectorProfile06.classValues.getD c.1 0) := by
  decide +kernel

private theorem a15MinedProjectorProfile06_countCases
    (s : A15EligibleIndex a15MinedProjectorProfile06.centroidVector) :
    let r0 := a15ProjectorClassCount
      a15MinedProjectorProfile06.classSizes (a15FourSubsetAt s.1) 0
    let r1 := a15ProjectorClassCount
      a15MinedProjectorProfile06.classSizes (a15FourSubsetAt s.1) 1
    (a15SubsetSum a15MinedProjectorProfile06.centroidVector s.1 = 60 →
        r0 = 0 ∧ (r1 = 0 ∨ r1 = 1)) ∧
      (a15SubsetSum a15MinedProjectorProfile06.centroidVector s.1 = -60 →
        (r0 = 1 ∧ r1 = 3) ∨ (r0 = 2 ∧ r1 = 1)) := by
  let r0 := a15ProjectorClassCount
    a15MinedProjectorProfile06.classSizes (a15FourSubsetAt s.1) 0
  let r1 := a15ProjectorClassCount
    a15MinedProjectorProfile06.classSizes (a15FourSubsetAt s.1) 1
  let r2 := a15ProjectorClassCount
    a15MinedProjectorProfile06.classSizes (a15FourSubsetAt s.1) 2
  let r3 := a15ProjectorClassCount
    a15MinedProjectorProfile06.classSizes (a15FourSubsetAt s.1) 3
  have hsum := a15MinedProjectorProfile06.sum_classCounts
    a15MinedProjectorProfile06_static.2.1 s.1
  have hweighted := a15MinedProjectorProfile06.weighted_classCounts
    a15MinedProjectorProfile06_static.2.1
    (fun c => (a15MinedProjectorProfile06_static.2.2 c).2) s.1
  have h0 := a15MinedProjectorProfile06.classCount_le_classSize
    ⟨0, by decide⟩ s.1
      (a15MinedProjectorProfile06_static.2.2 ⟨0, by decide⟩).1
  have h1 := a15MinedProjectorProfile06.classCount_le_classSize
    ⟨1, by decide⟩ s.1
      (a15MinedProjectorProfile06_static.2.2 ⟨1, by decide⟩).1
  have h2 := a15MinedProjectorProfile06.classCount_le_classSize
    ⟨2, by decide⟩ s.1
      (a15MinedProjectorProfile06_static.2.2 ⟨2, by decide⟩).1
  have h3 := a15MinedProjectorProfile06.classCount_le_classSize
    ⟨3, by decide⟩ s.1
      (a15MinedProjectorProfile06_static.2.2 ⟨3, by decide⟩).1
  change (∑ c : Fin 4,
    a15ProjectorClassCount #[2, 6, 6, 2]
      (a15FourSubsetAt s.1) c.1) = 4 at hsum
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hsum
  norm_num at hsum
  change (∑ c : Fin 4,
    (#[(-30 : ℤ), -10, 10, 30].getD c.1 0 : ℤ) *
      a15ProjectorClassCount #[2, 6, 6, 2]
        (a15FourSubsetAt s.1) c.1) = _ at hweighted
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hweighted
  norm_num at hweighted
  norm_num [a15MinedProjectorProfile06] at h0 h1 h2 h3
  change
    (a15SubsetSum a15MinedProjectorProfile06.centroidVector s.1 = 60 →
        a15ProjectorClassCount #[2, 6, 6, 2]
            (a15FourSubsetAt s.1) 0 = 0 ∧
          (a15ProjectorClassCount #[2, 6, 6, 2]
              (a15FourSubsetAt s.1) 1 = 0 ∨
            a15ProjectorClassCount #[2, 6, 6, 2]
              (a15FourSubsetAt s.1) 1 = 1)) ∧
      (a15SubsetSum a15MinedProjectorProfile06.centroidVector s.1 = -60 →
        (a15ProjectorClassCount #[2, 6, 6, 2]
              (a15FourSubsetAt s.1) 0 = 1 ∧
            a15ProjectorClassCount #[2, 6, 6, 2]
              (a15FourSubsetAt s.1) 1 = 3) ∨
          (a15ProjectorClassCount #[2, 6, 6, 2]
              (a15FourSubsetAt s.1) 0 = 2 ∧
            a15ProjectorClassCount #[2, 6, 6, 2]
              (a15FourSubsetAt s.1) 1 = 1))
  constructor <;> intro heligible <;> omega

private theorem a15MinedProjectorProfile06_classSquare
    (s : A15EligibleIndex a15MinedProjectorProfile06.centroidVector) :
    (∑ i ∈ a15MinedProjectorProfile06.classFinset 1,
      a15ProjectorShellCoordinate a15MinedProjectorProfile06.d
        (a15FourSubsetAt s.1) i) ^ 2 =
      -28 - 8 *
        (∑ i ∈ a15MinedProjectorProfile06.classFinset 0,
          a15ProjectorShellCoordinate a15MinedProjectorProfile06.d
            (a15FourSubsetAt s.1) i) -
        8 *
        (∑ i ∈ a15MinedProjectorProfile06.classFinset 1,
          a15ProjectorShellCoordinate a15MinedProjectorProfile06.d
            (a15FourSubsetAt s.1) i) := by
  have hclass1 := a15MinedProjectorProfile06.sum_shellCoordinate_class s 1
  have hclass0 := a15MinedProjectorProfile06.sum_shellCoordinate_class s 0
  have hcases := a15MinedProjectorProfile06_countCases s
  rw [hclass1, hclass0, ← a15ProjectorClassCount_eq_card,
    ← a15ProjectorClassCount_eq_card]
  rw [show (a15MinedProjectorProfile06.classFinset 1).card = 6 by decide,
    show (a15MinedProjectorProfile06.classFinset 0).card = 2 by decide]
  dsimp only at hcases
  rcases s.2 with hneg | hpos
  · have hsum :
        a15SubsetSum a15MinedProjectorProfile06.centroidVector s.1 = -60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hneg
    rcases hcases.2 hsum with ⟨hr0, hr1⟩ | ⟨hr0, hr1⟩
    · simp [show a15SubsetSum
          a15MinedProjectorProfile06.centroidVector s.1 ≠ 60 by omega,
        hr0, hr1]
    · simp [show a15SubsetSum
          a15MinedProjectorProfile06.centroidVector s.1 ≠ 60 by omega,
        hr0, hr1]
  · have hsum :
        a15SubsetSum a15MinedProjectorProfile06.centroidVector s.1 = 60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hpos
    rcases hcases.1 hsum with ⟨hr0, hr1 | hr1⟩
    · simp [hsum, hr0, hr1]
    · simp [hsum, hr0, hr1]

private theorem a15MinedProjectorProfile06_indicatorSquare
    (s : A15EligibleIndex a15MinedProjectorProfile06.centroidVector) :
    (a15MinedProjectorProfile06.shellDot
      (a15ClassIndicator a15MinedProjectorProfile06 1) s) ^ 2 =
      -28 - 8 *
        (∑ i ∈ a15MinedProjectorProfile06.classFinset 0,
          a15ProjectorShellCoordinate a15MinedProjectorProfile06.d
            (a15FourSubsetAt s.1) i) -
        8 *
        (∑ i ∈ a15MinedProjectorProfile06.classFinset 1,
          a15ProjectorShellCoordinate a15MinedProjectorProfile06.d
            (a15FourSubsetAt s.1) i) := by
  rw [a15MinedProjectorProfile06.shellDot_classIndicator]
  exact a15MinedProjectorProfile06_classSquare s

private theorem a15MinedProjectorProfile06_baseQForm :
    a15MinedProjectorProfile06.baseQForm
      (a15ClassIndicator a15MinedProjectorProfile06 1)
      (a15ClassIndicator a15MinedProjectorProfile06 1) = 23 / 4 := by
  rw [a15MinedProjectorProfile06.baseQForm_classIndicator]
  have hcard :
      (a15MinedProjectorProfile06.classFinset 1).card = 6 :=
    (a15MinedProjectorProfile06_static.2.2 ⟨1, by decide⟩).1
  have hsum :
      (∑ i ∈ a15MinedProjectorProfile06.classFinset 1,
        (a15MinedProjectorProfile06.centroidVector i : ℚ)) = -60 := by
    calc
      _ = ∑ _i ∈ a15MinedProjectorProfile06.classFinset 1,
          (-10 : ℚ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hic : a15MinedProjectorProfile06.inClass 1 i :=
          (Finset.mem_filter.mp hi).2
        rw [(a15MinedProjectorProfile06_static.2.2
          ⟨1, by decide⟩).2 i hic]
        norm_num [a15MinedProjectorProfile06]
      _ = -60 := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; norm_num
  rw [hcard, hsum]
  norm_num

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Profile 6 has no direct A15 shell realization. -/
theorem a15MinedProjectorProfile06_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      a15MinedProjectorProfile06.centroidVector) : False := by
  let finite := realization.toFiniteShell G
  let indicator := a15ClassIndicator a15MinedProjectorProfile06 1
  have htotal :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile06.centroidVector,
        (finite.multiplicity G s : ℤ)) = 220 := by
    rw [← Nat.cast_sum, finite.sum_multiplicity G,
      secondSubconstituent_card G hG x]
    norm_num
  have hclass0Total :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile06.centroidVector,
        (finite.multiplicity G s : ℤ) *
          (∑ i ∈ a15MinedProjectorProfile06.classFinset 0,
            a15ProjectorShellCoordinate a15MinedProjectorProfile06.d
              (a15FourSubsetAt s.1) i)) = -660 := by
    rw [realization.sum_multiplicity_shellClassSum G
      a15MinedProjectorProfile06 0]
    decide
  have hclass1Total :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile06.centroidVector,
        (finite.multiplicity G s : ℤ) *
          (∑ i ∈ a15MinedProjectorProfile06.classFinset 1,
            a15ProjectorShellCoordinate a15MinedProjectorProfile06.d
              (a15FourSubsetAt s.1) i)) = -660 := by
    rw [realization.sum_multiplicity_shellClassSum G
      a15MinedProjectorProfile06 1]
    decide
  have hsquaresInt :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile06.centroidVector,
        (finite.multiplicity G s : ℤ) *
          (a15MinedProjectorProfile06.shellDot indicator s) ^ 2) = 4400 := by
    dsimp only [indicator]
    simp_rw [a15MinedProjectorProfile06_indicatorSquare]
    calc
      _ = ∑ s : A15EligibleIndex
            a15MinedProjectorProfile06.centroidVector,
          (-28 * (finite.multiplicity G s : ℤ) -
            8 * ((finite.multiplicity G s : ℤ) *
              (∑ i ∈ a15MinedProjectorProfile06.classFinset 0,
                a15ProjectorShellCoordinate a15MinedProjectorProfile06.d
                  (a15FourSubsetAt s.1) i)) -
            8 * ((finite.multiplicity G s : ℤ) *
              (∑ i ∈ a15MinedProjectorProfile06.classFinset 1,
                a15ProjectorShellCoordinate a15MinedProjectorProfile06.d
                  (a15FourSubsetAt s.1) i))) := by
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = -28 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile06.centroidVector,
            (finite.multiplicity G s : ℤ)) -
          8 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile06.centroidVector,
            (finite.multiplicity G s : ℤ) *
              (∑ i ∈ a15MinedProjectorProfile06.classFinset 0,
                a15ProjectorShellCoordinate a15MinedProjectorProfile06.d
                  (a15FourSubsetAt s.1) i)) -
          8 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile06.centroidVector,
            (finite.multiplicity G s : ℤ) *
              (∑ i ∈ a15MinedProjectorProfile06.classFinset 1,
                a15ProjectorShellCoordinate a15MinedProjectorProfile06.d
                  (a15FourSubsetAt s.1) i)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 4400 := by
        rw [htotal, hclass0Total, hclass1Total]
        norm_num
  have hsquares :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile06.centroidVector,
        (finite.multiplicity G s : ℚ) *
          (a15MinedProjectorProfile06.shellDot indicator s : ℚ) ^ 2) =
        4400 := by
    exact_mod_cast hsquaresInt
  have hqform :
      a15RationalMatrixQForm (realization.complementProjector G)
        (a15ProjectorArrayVector indicator)
        (a15ProjectorArrayVector indicator) = -13 / 36 := by
    rw [a15DirectQForm_expand G a15MinedProjectorProfile06 realization,
      a15MinedProjectorProfile06_baseQForm]
    have hsquares' :
        (∑ s : A15EligibleIndex a15MinedProjectorProfile06.centroidVector,
          (finite.multiplicity G s : ℚ) *
            a15MinedProjectorProfile06.shellDot indicator s *
            a15MinedProjectorProfile06.shellDot indicator s) = 4400 := by
      simpa [pow_two, mul_assoc] using hsquares
    rw [hsquares']
    norm_num
  have hnonneg := a15RationalMatrixQForm_self_nonneg
    (realization.complementProjector_posSemidef G hG x
      a15MinedProjectorProfile06_static.1)
    (a15ProjectorArrayVector indicator)
  rw [hqform] at hnonneg
  norm_num at hnonneg

/-- Mined norm profile 8 is the class-only profile 6 and is impossible. -/
theorem a15MinedNormProfile08_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      (a15SmallProfile a15MinedNormProfile08)) : False := by
  have hrealization : A15ShellGramRealization G x
      a15MinedProjectorProfile06.centroidVector :=
    a15MinedProjectorProfile06_centroidVector.symm ▸ realization
  exact a15MinedProjectorProfile06_no_realization G hG x hrealization

end SRG266
