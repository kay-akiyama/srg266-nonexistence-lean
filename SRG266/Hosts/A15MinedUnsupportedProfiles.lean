/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15MinedProjectorTheory
import SRG266.Hosts.A15MinedNormProfileData
import SRG266.Hosts.A15MinedSearch

/-!
# Intrinsic exclusions of the two unsupported mined A15 profiles

Norm profiles 1 and 10 are removed by an eligible-cardinality
computation.  Their two coordinate classes make the stronger fact immediate:
no four-subset has centroid sum `-60` or `60`.  Hence neither profile admits a
direct shell realization.
-/

open scoped BigOperators

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def a15MinedUnsupportedProfile01 : A15ProjectorProfile where
  centroidIndex := 1
  d := #[-10, -10, -10, -10, -10, -10, -10, -10,
    -10, -10, -10, -10, 30, 30, 30, 30]
  reportedEligible := 0
  classValues := #[-10, 30]
  classSizes := #[12, 4]
  orbits := #[]

def a15MinedUnsupportedProfile10 : A15ProjectorProfile where
  centroidIndex := 10
  d := #[-30, -30, -30, -30,
    10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10]
  reportedEligible := 0
  classValues := #[-30, 10]
  classSizes := #[4, 12]
  orbits := #[]

theorem a15MinedUnsupportedProfile01_centroidVector :
    a15MinedUnsupportedProfile01.centroidVector =
      a15SmallProfile a15MinedNormProfile01 := by
  funext i
  fin_cases i <;> rfl

theorem a15MinedUnsupportedProfile10_centroidVector :
    a15MinedUnsupportedProfile10.centroidVector =
      a15SmallProfile a15MinedNormProfile10 := by
  funext i
  fin_cases i <;> rfl

private theorem a15MinedUnsupportedProfile01_static :
    (∀ i, a15MinedUnsupportedProfile01.classIndexCount i = 1) ∧
    (∀ c : Fin a15MinedUnsupportedProfile01.classSizes.size,
      ∀ i, a15MinedUnsupportedProfile01.inClass c.1 i →
        a15MinedUnsupportedProfile01.centroidVector i =
          a15MinedUnsupportedProfile01.classValues.getD c.1 0) := by
  decide +kernel

private theorem a15MinedUnsupportedProfile10_static :
    (∀ i, a15MinedUnsupportedProfile10.classIndexCount i = 1) ∧
    (∀ c : Fin a15MinedUnsupportedProfile10.classSizes.size,
      ∀ i, a15MinedUnsupportedProfile10.inClass c.1 i →
        a15MinedUnsupportedProfile10.centroidVector i =
          a15MinedUnsupportedProfile10.classValues.getD c.1 0) := by
  decide +kernel

theorem a15MinedUnsupportedProfile01_no_eligible
    (s : A15EligibleIndex a15MinedUnsupportedProfile01.centroidVector) :
    False := by
  have hsum := a15MinedUnsupportedProfile01.sum_classCounts
    a15MinedUnsupportedProfile01_static.1 s.1
  have hweighted := a15MinedUnsupportedProfile01.weighted_classCounts
    a15MinedUnsupportedProfile01_static.1
    a15MinedUnsupportedProfile01_static.2 s.1
  have heligible :
      a15SubsetSum a15MinedUnsupportedProfile01.centroidVector s.1 = -60 ∨
      a15SubsetSum a15MinedUnsupportedProfile01.centroidVector s.1 = 60 := by
    simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using s.2
  change (∑ c : Fin 2,
    a15ProjectorClassCount #[12, 4]
      (a15FourSubsetAt s.1) c.1) = 4 at hsum
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hsum
  norm_num at hsum
  change (∑ c : Fin 2,
    (#[(-10 : ℤ), 30].getD c.1 0 : ℤ) *
      a15ProjectorClassCount #[12, 4]
        (a15FourSubsetAt s.1) c.1) = _ at hweighted
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hweighted
  norm_num at hweighted
  rcases heligible with hneg | hpos <;> omega

theorem a15MinedUnsupportedProfile10_no_eligible
    (s : A15EligibleIndex a15MinedUnsupportedProfile10.centroidVector) :
    False := by
  have hsum := a15MinedUnsupportedProfile10.sum_classCounts
    a15MinedUnsupportedProfile10_static.1 s.1
  have hweighted := a15MinedUnsupportedProfile10.weighted_classCounts
    a15MinedUnsupportedProfile10_static.1
    a15MinedUnsupportedProfile10_static.2 s.1
  have heligible :
      a15SubsetSum a15MinedUnsupportedProfile10.centroidVector s.1 = -60 ∨
      a15SubsetSum a15MinedUnsupportedProfile10.centroidVector s.1 = 60 := by
    simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using s.2
  change (∑ c : Fin 2,
    a15ProjectorClassCount #[4, 12]
      (a15FourSubsetAt s.1) c.1) = 4 at hsum
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hsum
  norm_num at hsum
  change (∑ c : Fin 2,
    (#[(-30 : ℤ), 10].getD c.1 0 : ℤ) *
      a15ProjectorClassCount #[4, 12]
        (a15FourSubsetAt s.1) c.1) = _ at hweighted
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hweighted
  norm_num at hweighted
  rcases heligible with hneg | hpos <;> omega

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem a15MinedNormProfile01_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      (a15SmallProfile a15MinedNormProfile01)) : False := by
  have hrealization : A15ShellGramRealization G x
      a15MinedUnsupportedProfile01.centroidVector :=
    a15MinedUnsupportedProfile01_centroidVector.symm ▸ realization
  letI : Nonempty (SecondSubconstituent G x) :=
    Fintype.card_pos_iff.mp (by
      rw [secondSubconstituent_card G hG x]
      norm_num)
  obtain ⟨B⟩ : Nonempty (SecondSubconstituent G x) := inferInstance
  exact a15MinedUnsupportedProfile01_no_eligible (hrealization.shell B)

theorem a15MinedNormProfile10_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      (a15SmallProfile a15MinedNormProfile10)) : False := by
  have hrealization : A15ShellGramRealization G x
      a15MinedUnsupportedProfile10.centroidVector :=
    a15MinedUnsupportedProfile10_centroidVector.symm ▸ realization
  letI : Nonempty (SecondSubconstituent G x) :=
    Fintype.card_pos_iff.mp (by
      rw [secondSubconstituent_card G hG x]
      norm_num)
  obtain ⟨B⟩ : Nonempty (SecondSubconstituent G x) := inferInstance
  exact a15MinedUnsupportedProfile10_no_eligible (hrealization.shell B)

end SRG266
