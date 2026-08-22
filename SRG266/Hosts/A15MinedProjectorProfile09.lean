/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15MinedProjectorTheory
import SRG266.Hosts.A15MinedNormProfileData
import SRG266.Hosts.A15MinedSearch

/-!
# Mined exclusion of A15 projector profile 9

The certificate rejects 221 orbit-total candidates.  Every
eligible four-subset meets the four zero coordinates in exactly one point,
so the sum of standard coordinate-difference projector forms on that class
is the fixed negative number `-16/3`.  Positive semidefiniteness excludes the
profile without importing any orbit moment or rejection table.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The class-only skeleton of generated projector profile 9. -/
def a15MinedProjectorProfile09 : A15ProjectorProfile where
  centroidIndex := 9
  d := #[-20, -20, -20, -20, -20, -20,
    0, 0, 0, 0,
    20, 20, 20, 20, 20, 20]
  reportedEligible := 160
  classValues := #[-20, 0, 20]
  classSizes := #[6, 4, 6]
  orbits := #[]

theorem a15MinedProjectorProfile09_centroidVector :
    a15MinedProjectorProfile09.centroidVector =
      a15SmallProfile a15MinedNormProfile05 := by
  funext i
  fin_cases i <;> rfl

private theorem a15MinedProjectorProfile09_static :
    (∑ i, a15MinedProjectorProfile09.centroidVector i) = 0 ∧
    (∀ i, a15MinedProjectorProfile09.classIndexCount i = 1) ∧
    (∀ c : Fin a15MinedProjectorProfile09.classSizes.size,
      (a15MinedProjectorProfile09.classFinset c.1).card =
        a15MinedProjectorProfile09.classSizes.getD c.1 0 ∧
      ∀ i, a15MinedProjectorProfile09.inClass c.1 i →
        a15MinedProjectorProfile09.centroidVector i =
          a15MinedProjectorProfile09.classValues.getD c.1 0) := by
  decide +kernel

private theorem a15MinedProjectorProfile09_middleCount
    (s : A15EligibleIndex a15MinedProjectorProfile09.centroidVector) :
    a15ProjectorClassCount a15MinedProjectorProfile09.classSizes
        (a15FourSubsetAt s.1) 1 = 1 := by
  let r0 := a15ProjectorClassCount
    a15MinedProjectorProfile09.classSizes (a15FourSubsetAt s.1) 0
  let r1 := a15ProjectorClassCount
    a15MinedProjectorProfile09.classSizes (a15FourSubsetAt s.1) 1
  let r2 := a15ProjectorClassCount
    a15MinedProjectorProfile09.classSizes (a15FourSubsetAt s.1) 2
  have hsum := a15MinedProjectorProfile09.sum_classCounts
    a15MinedProjectorProfile09_static.2.1 s.1
  have hweighted := a15MinedProjectorProfile09.weighted_classCounts
    a15MinedProjectorProfile09_static.2.1
    (fun c => (a15MinedProjectorProfile09_static.2.2 c).2) s.1
  have heligible :
      a15SubsetSum a15MinedProjectorProfile09.centroidVector s.1 = -60 ∨
      a15SubsetSum a15MinedProjectorProfile09.centroidVector s.1 = 60 :=
    s.2
  have hsum' : r0 + r1 + r2 = 4 := by
    change (∑ c : Fin 3,
      a15ProjectorClassCount #[6, 4, 6]
        (a15FourSubsetAt s.1) c.1) = 4 at hsum
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hsum
    norm_num at hsum
    dsimp [a15MinedProjectorProfile09, r0, r1, r2]
    omega
  have hweighted' :
      (-20 : ℤ) * r0 + 0 * r1 + 20 * r2 =
        a15SubsetSum a15MinedProjectorProfile09.centroidVector s.1 := by
    change (∑ c : Fin 3,
      (#[(-20 : ℤ), 0, 20].getD c.1 0 : ℤ) *
        a15ProjectorClassCount #[6, 4, 6]
          (a15FourSubsetAt s.1) c.1) = _ at hweighted
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hweighted
    simpa [a15MinedProjectorProfile09, r0, r1, r2] using hweighted
  change r1 = 1
  omega

private theorem a15MinedProjectorProfile09_middleMoment
    (s : A15EligibleIndex a15MinedProjectorProfile09.centroidVector) :
    a15MinedProjectorProfile09.shellDifferenceMoment 1 s = 96 := by
  rw [A15ProjectorProfile.shellDifferenceMoment_eq_card]
  rw [← a15ProjectorClassCount_eq_card]
  rw [a15MinedProjectorProfile09_middleCount s]
  rw [(a15MinedProjectorProfile09_static.2.2 ⟨1, by decide⟩).1]
  norm_num [a15MinedProjectorProfile09]

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Profile 9 has no direct A15 shell realization. -/
theorem a15MinedProjectorProfile09_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      a15MinedProjectorProfile09.centroidVector) : False := by
  apply realization.no_realization_of_constant_classMoment
    G hG x a15MinedProjectorProfile09 ⟨1, by decide⟩
    a15MinedProjectorProfile09_static.1 (by decide)
    (a15MinedProjectorProfile09_static.2.2 ⟨1, by decide⟩).1
    (a15MinedProjectorProfile09_static.2.2 ⟨1, by decide⟩).2
    96 a15MinedProjectorProfile09_middleMoment
  norm_num [a15MinedProjectorProfile09]

/-- The fifth mined norm profile is the class-only profile 9 and is therefore
impossible. -/
theorem a15MinedNormProfile05_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      (a15SmallProfile a15MinedNormProfile05)) : False := by
  have hrealization : A15ShellGramRealization G x
      a15MinedProjectorProfile09.centroidVector :=
    a15MinedProjectorProfile09_centroidVector.symm ▸ realization
  exact a15MinedProjectorProfile09_no_realization G hG x hrealization

end SRG266
