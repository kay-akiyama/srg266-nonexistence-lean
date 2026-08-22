/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15MinedProjectorTheory
import SRG266.Hosts.A15MinedNormProfileData
import SRG266.Hosts.A15MinedSearch

/-!
# Mined exclusion of A15 projector profile 4

The certificate rejects seven orbit-total candidates with the same
standard coordinate difference.  The centroid equations determine the total
class-difference moment directly: the two-coordinate `-20` class contributes
`3520`.  Its ordered-pair projector sum is therefore negative, with no orbit
table, membership audit, or rejection list.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The class-only skeleton of generated projector profile 4. -/
def a15MinedProjectorProfile04 : A15ProjectorProfile where
  centroidIndex := 4
  d := #[-40, -20, -20,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    20, 20, 40]
  reportedEligible := 184
  classValues := #[-40, -20, 0, 20, 40]
  classSizes := #[1, 2, 10, 2, 1]
  orbits := #[]

theorem a15MinedProjectorProfile04_centroidVector :
    a15MinedProjectorProfile04.centroidVector =
      a15SmallProfile a15MinedNormProfile11 := by
  funext i
  fin_cases i <;> rfl

private theorem a15MinedProjectorProfile04_static :
    (∑ i, a15MinedProjectorProfile04.centroidVector i) = 0 ∧
    (∀ i, a15MinedProjectorProfile04.classIndexCount i = 1) ∧
    (∀ c : Fin a15MinedProjectorProfile04.classSizes.size,
      (a15MinedProjectorProfile04.classFinset c.1).card =
        a15MinedProjectorProfile04.classSizes.getD c.1 0 ∧
      ∀ i, a15MinedProjectorProfile04.inClass c.1 i →
        a15MinedProjectorProfile04.centroidVector i =
          a15MinedProjectorProfile04.classValues.getD c.1 0) := by
  decide +kernel

private theorem a15MinedProjectorProfile04_countCases
    (s : A15EligibleIndex a15MinedProjectorProfile04.centroidVector) :
    let r0 := a15ProjectorClassCount
      a15MinedProjectorProfile04.classSizes (a15FourSubsetAt s.1) 0
    let r1 := a15ProjectorClassCount
      a15MinedProjectorProfile04.classSizes (a15FourSubsetAt s.1) 1
    (a15SubsetSum a15MinedProjectorProfile04.centroidVector s.1 = 60 →
        r0 = 0 ∧ (r1 = 0 ∨ r1 = 1)) ∧
      (a15SubsetSum a15MinedProjectorProfile04.centroidVector s.1 = -60 →
        r0 = 1 ∧ (r1 = 1 ∨ r1 = 2)) := by
  let r0 := a15ProjectorClassCount
    a15MinedProjectorProfile04.classSizes (a15FourSubsetAt s.1) 0
  let r1 := a15ProjectorClassCount
    a15MinedProjectorProfile04.classSizes (a15FourSubsetAt s.1) 1
  let r2 := a15ProjectorClassCount
    a15MinedProjectorProfile04.classSizes (a15FourSubsetAt s.1) 2
  let r3 := a15ProjectorClassCount
    a15MinedProjectorProfile04.classSizes (a15FourSubsetAt s.1) 3
  let r4 := a15ProjectorClassCount
    a15MinedProjectorProfile04.classSizes (a15FourSubsetAt s.1) 4
  have hsum := a15MinedProjectorProfile04.sum_classCounts
    a15MinedProjectorProfile04_static.2.1 s.1
  have hweighted := a15MinedProjectorProfile04.weighted_classCounts
    a15MinedProjectorProfile04_static.2.1
    (fun c => (a15MinedProjectorProfile04_static.2.2 c).2) s.1
  have h0 := a15MinedProjectorProfile04.classCount_le_classSize
    ⟨0, by decide⟩ s.1 (a15MinedProjectorProfile04_static.2.2 ⟨0, by decide⟩).1
  have h1 := a15MinedProjectorProfile04.classCount_le_classSize
    ⟨1, by decide⟩ s.1 (a15MinedProjectorProfile04_static.2.2 ⟨1, by decide⟩).1
  have h3 := a15MinedProjectorProfile04.classCount_le_classSize
    ⟨3, by decide⟩ s.1 (a15MinedProjectorProfile04_static.2.2 ⟨3, by decide⟩).1
  have h4 := a15MinedProjectorProfile04.classCount_le_classSize
    ⟨4, by decide⟩ s.1 (a15MinedProjectorProfile04_static.2.2 ⟨4, by decide⟩).1
  change (∑ c : Fin 5,
    a15ProjectorClassCount #[1, 2, 10, 2, 1]
      (a15FourSubsetAt s.1) c.1) = 4 at hsum
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hsum
  norm_num at hsum
  change (∑ c : Fin 5,
    (#[(-40 : ℤ), -20, 0, 20, 40].getD c.1 0 : ℤ) *
      a15ProjectorClassCount #[1, 2, 10, 2, 1]
        (a15FourSubsetAt s.1) c.1) = _ at hweighted
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hweighted
  norm_num at hweighted
  norm_num [a15MinedProjectorProfile04] at h0 h1 h3 h4
  change
    (a15SubsetSum a15MinedProjectorProfile04.centroidVector s.1 = 60 →
        a15ProjectorClassCount #[1, 2, 10, 2, 1]
          (a15FourSubsetAt s.1) 0 = 0 ∧
        (a15ProjectorClassCount #[1, 2, 10, 2, 1]
            (a15FourSubsetAt s.1) 1 = 0 ∨
          a15ProjectorClassCount #[1, 2, 10, 2, 1]
            (a15FourSubsetAt s.1) 1 = 1)) ∧
      (a15SubsetSum a15MinedProjectorProfile04.centroidVector s.1 = -60 →
        a15ProjectorClassCount #[1, 2, 10, 2, 1]
          (a15FourSubsetAt s.1) 0 = 1 ∧
        (a15ProjectorClassCount #[1, 2, 10, 2, 1]
            (a15FourSubsetAt s.1) 1 = 1 ∨
          a15ProjectorClassCount #[1, 2, 10, 2, 1]
            (a15FourSubsetAt s.1) 1 = 2))
  constructor <;> intro heligible <;> constructor <;> omega

private theorem a15MinedProjectorProfile04_pointwiseMoment
    (s : A15EligibleIndex a15MinedProjectorProfile04.centroidVector) :
    a15MinedProjectorProfile04.shellDifferenceMoment 1 s =
      8 * (∑ i ∈ a15MinedProjectorProfile04.classFinset 1,
        a15ProjectorShellCoordinate a15MinedProjectorProfile04.d
          (a15FourSubsetAt s.1) i) -
      16 * (∑ i ∈ a15MinedProjectorProfile04.classFinset 0,
        a15ProjectorShellCoordinate a15MinedProjectorProfile04.d
          (a15FourSubsetAt s.1) i) := by
  have hclass1 := a15MinedProjectorProfile04.sum_shellCoordinate_class s 1
  have hclass0 := a15MinedProjectorProfile04.sum_shellCoordinate_class s 0
  have hcases := a15MinedProjectorProfile04_countCases s
  rw [A15ProjectorProfile.shellDifferenceMoment_eq_card,
    ← a15ProjectorClassCount_eq_card]
  rw [hclass1, hclass0, ← a15ProjectorClassCount_eq_card,
    ← a15ProjectorClassCount_eq_card]
  rw [show (a15MinedProjectorProfile04.classFinset 1).card = 2 by decide,
    show (a15MinedProjectorProfile04.classFinset 0).card = 1 by decide]
  dsimp only at hcases
  rcases s.2 with hneg | hpos
  · have hsum :
        a15SubsetSum a15MinedProjectorProfile04.centroidVector s.1 = -60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hneg
    rcases hcases.2 hsum with ⟨hr0, hr1 | hr1⟩
    · simp [show a15SubsetSum
          a15MinedProjectorProfile04.centroidVector s.1 ≠ 60 by omega,
        hr0, hr1]
    · simp [show a15SubsetSum
          a15MinedProjectorProfile04.centroidVector s.1 ≠ 60 by omega,
        hr0, hr1]
  · have hsum :
        a15SubsetSum a15MinedProjectorProfile04.centroidVector s.1 = 60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hpos
    rcases hcases.1 hsum with ⟨hr0, hr1 | hr1⟩
    · simp [hsum, hr0, hr1]
    · simp [hsum, hr0, hr1]

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Profile 4 has no direct A15 shell realization. -/
theorem a15MinedProjectorProfile04_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      a15MinedProjectorProfile04.centroidVector) : False := by
  let finite := realization.toFiniteShell G
  have hclass1Total :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile04.centroidVector,
        (finite.multiplicity G s : ℤ) *
          (∑ i ∈ a15MinedProjectorProfile04.classFinset 1,
            a15ProjectorShellCoordinate a15MinedProjectorProfile04.d
              (a15FourSubsetAt s.1) i)) = -440 := by
    rw [realization.sum_multiplicity_shellClassSum G
      a15MinedProjectorProfile04 1]
    decide
  have hclass0Total :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile04.centroidVector,
        (finite.multiplicity G s : ℤ) *
          (∑ i ∈ a15MinedProjectorProfile04.classFinset 0,
            a15ProjectorShellCoordinate a15MinedProjectorProfile04.d
              (a15FourSubsetAt s.1) i)) = -440 := by
    rw [realization.sum_multiplicity_shellClassSum G
      a15MinedProjectorProfile04 0]
    decide
  have hmomentSumInt :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile04.centroidVector,
        (finite.multiplicity G s : ℤ) *
          a15MinedProjectorProfile04.shellDifferenceMoment 1 s) = 3520 := by
    simp_rw [a15MinedProjectorProfile04_pointwiseMoment]
    calc
      _ = 8 * (∑ s : A15EligibleIndex
            a15MinedProjectorProfile04.centroidVector,
          (finite.multiplicity G s : ℤ) *
            (∑ i ∈ a15MinedProjectorProfile04.classFinset 1,
              a15ProjectorShellCoordinate a15MinedProjectorProfile04.d
                (a15FourSubsetAt s.1) i)) -
          16 * (∑ s : A15EligibleIndex
            a15MinedProjectorProfile04.centroidVector,
          (finite.multiplicity G s : ℤ) *
            (∑ i ∈ a15MinedProjectorProfile04.classFinset 0,
              a15ProjectorShellCoordinate a15MinedProjectorProfile04.d
                (a15FourSubsetAt s.1) i)) := by
        calc
          _ = ∑ s : A15EligibleIndex
                a15MinedProjectorProfile04.centroidVector,
              (8 * ((finite.multiplicity G s : ℤ) *
                (∑ i ∈ a15MinedProjectorProfile04.classFinset 1,
                  a15ProjectorShellCoordinate
                    a15MinedProjectorProfile04.d
                    (a15FourSubsetAt s.1) i)) -
              16 * ((finite.multiplicity G s : ℤ) *
                (∑ i ∈ a15MinedProjectorProfile04.classFinset 0,
                  a15ProjectorShellCoordinate
                    a15MinedProjectorProfile04.d
                    (a15FourSubsetAt s.1) i))) := by
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = _ := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum]
      _ = 3520 := by rw [hclass1Total, hclass0Total]; norm_num
  have hmomentSum :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile04.centroidVector,
        (finite.multiplicity G s : ℚ) *
          (a15MinedProjectorProfile04.shellDifferenceMoment 1 s : ℚ)) =
        3520 := by
    exact_mod_cast hmomentSumInt
  apply realization.no_realization_of_classMomentSum
    G hG x a15MinedProjectorProfile04 ⟨1, by decide⟩
    a15MinedProjectorProfile04_static.1 (by decide)
    (a15MinedProjectorProfile04_static.2.2 ⟨1, by decide⟩).1
    (a15MinedProjectorProfile04_static.2.2 ⟨1, by decide⟩).2
    3520 hmomentSum
  norm_num [a15MinedProjectorProfile04]

/-- Mined norm profile 11 is the class-only profile 4 and is impossible. -/
theorem a15MinedNormProfile11_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      (a15SmallProfile a15MinedNormProfile11)) : False := by
  have hrealization : A15ShellGramRealization G x
      a15MinedProjectorProfile04.centroidVector :=
    a15MinedProjectorProfile04_centroidVector.symm ▸ realization
  exact a15MinedProjectorProfile04_no_realization G hG x hrealization

end SRG266
