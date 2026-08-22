/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15MinedProjectorTheory
import SRG266.Hosts.A15MinedNormProfileData
import SRG266.Hosts.A15MinedSearch

/-!
# Constant-moment exclusions for A15 projector profiles 2 and 11

For both profiles the relevant four-coordinate class meets every eligible
four-subset in either one or three positions.  Its ordered coordinate-
difference moment is therefore always `96`, giving the same `-16/3`
projector contradiction as mined profile 9.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def a15MinedProjectorProfile02 : A15ProjectorProfile where
  centroidIndex := 2
  d := #[-40, -40,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    20, 20, 20, 20]
  reportedEligible := 80
  classValues := #[-40, 0, 20]
  classSizes := #[2, 10, 4]
  orbits := #[]

def a15MinedProjectorProfile11 : A15ProjectorProfile where
  centroidIndex := 11
  d := #[-20, -20, -20, -20,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    40, 40]
  reportedEligible := 80
  classValues := #[-20, 0, 40]
  classSizes := #[4, 10, 2]
  orbits := #[]

theorem a15MinedProjectorProfile02_centroidVector :
    a15MinedProjectorProfile02.centroidVector =
      a15SmallProfile a15MinedNormProfile13 := by
  funext i
  fin_cases i <;> rfl

theorem a15MinedProjectorProfile11_centroidVector :
    a15MinedProjectorProfile11.centroidVector =
      a15SmallProfile a15MinedNormProfile03 := by
  funext i
  fin_cases i <;> rfl

private theorem a15MinedProjectorProfile02_static :
    (∑ i, a15MinedProjectorProfile02.centroidVector i) = 0 ∧
    (∀ i, a15MinedProjectorProfile02.classIndexCount i = 1) ∧
    (∀ c : Fin a15MinedProjectorProfile02.classSizes.size,
      (a15MinedProjectorProfile02.classFinset c.1).card =
        a15MinedProjectorProfile02.classSizes.getD c.1 0 ∧
      ∀ i, a15MinedProjectorProfile02.inClass c.1 i →
        a15MinedProjectorProfile02.centroidVector i =
          a15MinedProjectorProfile02.classValues.getD c.1 0) := by
  decide +kernel

private theorem a15MinedProjectorProfile11_static :
    (∑ i, a15MinedProjectorProfile11.centroidVector i) = 0 ∧
    (∀ i, a15MinedProjectorProfile11.classIndexCount i = 1) ∧
    (∀ c : Fin a15MinedProjectorProfile11.classSizes.size,
      (a15MinedProjectorProfile11.classFinset c.1).card =
        a15MinedProjectorProfile11.classSizes.getD c.1 0 ∧
      ∀ i, a15MinedProjectorProfile11.inClass c.1 i →
        a15MinedProjectorProfile11.centroidVector i =
          a15MinedProjectorProfile11.classValues.getD c.1 0) := by
  decide +kernel

private theorem a15MinedProjectorProfile02_lastCount
    (s : A15EligibleIndex a15MinedProjectorProfile02.centroidVector) :
    a15ProjectorClassCount a15MinedProjectorProfile02.classSizes
        (a15FourSubsetAt s.1) 2 = 1 ∨
      a15ProjectorClassCount a15MinedProjectorProfile02.classSizes
        (a15FourSubsetAt s.1) 2 = 3 := by
  let r0 := a15ProjectorClassCount
    a15MinedProjectorProfile02.classSizes (a15FourSubsetAt s.1) 0
  let r1 := a15ProjectorClassCount
    a15MinedProjectorProfile02.classSizes (a15FourSubsetAt s.1) 1
  let r2 := a15ProjectorClassCount
    a15MinedProjectorProfile02.classSizes (a15FourSubsetAt s.1) 2
  have hsum := a15MinedProjectorProfile02.sum_classCounts
    a15MinedProjectorProfile02_static.2.1 s.1
  have hweighted := a15MinedProjectorProfile02.weighted_classCounts
    a15MinedProjectorProfile02_static.2.1
    (fun c => (a15MinedProjectorProfile02_static.2.2 c).2) s.1
  have heligible :
      a15SubsetSum a15MinedProjectorProfile02.centroidVector s.1 = -60 ∨
      a15SubsetSum a15MinedProjectorProfile02.centroidVector s.1 = 60 := s.2
  change (∑ c : Fin 3,
    a15ProjectorClassCount #[2, 10, 4]
      (a15FourSubsetAt s.1) c.1) = 4 at hsum
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hsum
  norm_num at hsum
  change (∑ c : Fin 3,
    (#[(-40 : ℤ), 0, 20].getD c.1 0 : ℤ) *
      a15ProjectorClassCount #[2, 10, 4]
        (a15FourSubsetAt s.1) c.1) = _ at hweighted
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hweighted
  norm_num at hweighted
  dsimp [a15MinedProjectorProfile02, r0, r1, r2] at ⊢
  omega

private theorem a15MinedProjectorProfile11_firstCount
    (s : A15EligibleIndex a15MinedProjectorProfile11.centroidVector) :
    a15ProjectorClassCount a15MinedProjectorProfile11.classSizes
        (a15FourSubsetAt s.1) 0 = 1 ∨
      a15ProjectorClassCount a15MinedProjectorProfile11.classSizes
        (a15FourSubsetAt s.1) 0 = 3 := by
  let r0 := a15ProjectorClassCount
    a15MinedProjectorProfile11.classSizes (a15FourSubsetAt s.1) 0
  let r1 := a15ProjectorClassCount
    a15MinedProjectorProfile11.classSizes (a15FourSubsetAt s.1) 1
  let r2 := a15ProjectorClassCount
    a15MinedProjectorProfile11.classSizes (a15FourSubsetAt s.1) 2
  have hsum := a15MinedProjectorProfile11.sum_classCounts
    a15MinedProjectorProfile11_static.2.1 s.1
  have hweighted := a15MinedProjectorProfile11.weighted_classCounts
    a15MinedProjectorProfile11_static.2.1
    (fun c => (a15MinedProjectorProfile11_static.2.2 c).2) s.1
  have heligible :
      a15SubsetSum a15MinedProjectorProfile11.centroidVector s.1 = -60 ∨
      a15SubsetSum a15MinedProjectorProfile11.centroidVector s.1 = 60 := s.2
  change (∑ c : Fin 3,
    a15ProjectorClassCount #[4, 10, 2]
      (a15FourSubsetAt s.1) c.1) = 4 at hsum
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hsum
  norm_num at hsum
  change (∑ c : Fin 3,
    (#[(-20 : ℤ), 0, 40].getD c.1 0 : ℤ) *
      a15ProjectorClassCount #[4, 10, 2]
        (a15FourSubsetAt s.1) c.1) = _ at hweighted
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hweighted
  norm_num at hweighted
  dsimp [a15MinedProjectorProfile11, r0, r1, r2] at ⊢
  omega

private theorem a15MinedProjectorProfile02_lastMoment
    (s : A15EligibleIndex a15MinedProjectorProfile02.centroidVector) :
    a15MinedProjectorProfile02.shellDifferenceMoment 2 s = 96 := by
  rw [A15ProjectorProfile.shellDifferenceMoment_eq_card]
  rw [← a15ProjectorClassCount_eq_card]
  rcases a15MinedProjectorProfile02_lastCount s with h | h <;> rw [h]
  <;> rw [(a15MinedProjectorProfile02_static.2.2 ⟨2, by decide⟩).1]
  <;> norm_num [a15MinedProjectorProfile02]

private theorem a15MinedProjectorProfile11_firstMoment
    (s : A15EligibleIndex a15MinedProjectorProfile11.centroidVector) :
    a15MinedProjectorProfile11.shellDifferenceMoment 0 s = 96 := by
  rw [A15ProjectorProfile.shellDifferenceMoment_eq_card]
  rw [← a15ProjectorClassCount_eq_card]
  rcases a15MinedProjectorProfile11_firstCount s with h | h <;> rw [h]
  <;> rw [(a15MinedProjectorProfile11_static.2.2 ⟨0, by decide⟩).1]
  <;> norm_num [a15MinedProjectorProfile11]

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem a15MinedNormProfile13_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      (a15SmallProfile a15MinedNormProfile13)) : False := by
  have hrealization : A15ShellGramRealization G x
      a15MinedProjectorProfile02.centroidVector :=
    a15MinedProjectorProfile02_centroidVector.symm ▸ realization
  apply hrealization.no_realization_of_constant_classMoment
    G hG x a15MinedProjectorProfile02 ⟨2, by decide⟩
    a15MinedProjectorProfile02_static.1 (by decide)
    (a15MinedProjectorProfile02_static.2.2 ⟨2, by decide⟩).1
    (a15MinedProjectorProfile02_static.2.2 ⟨2, by decide⟩).2
    96 a15MinedProjectorProfile02_lastMoment
  norm_num [a15MinedProjectorProfile02]

theorem a15MinedNormProfile03_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      (a15SmallProfile a15MinedNormProfile03)) : False := by
  have hrealization : A15ShellGramRealization G x
      a15MinedProjectorProfile11.centroidVector :=
    a15MinedProjectorProfile11_centroidVector.symm ▸ realization
  apply hrealization.no_realization_of_constant_classMoment
    G hG x a15MinedProjectorProfile11 ⟨0, by decide⟩
    a15MinedProjectorProfile11_static.1 (by decide)
    (a15MinedProjectorProfile11_static.2.2 ⟨0, by decide⟩).1
    (a15MinedProjectorProfile11_static.2.2 ⟨0, by decide⟩).2
    96 a15MinedProjectorProfile11_firstMoment
  norm_num [a15MinedProjectorProfile11]

end SRG266
