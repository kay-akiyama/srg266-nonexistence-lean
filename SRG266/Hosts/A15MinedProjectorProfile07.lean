/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15MinedProjectorProfile05

/-!
# Mined exclusion of A15 projector profile 7

This is the coordinate-reversed companion to profile 5.  Its relevant
three-coordinate class has total difference moment `10560 - 192 e`, where
`e ≤ 3` is the multiplicity of the unique extreme eligible four-subset.
No generated orbit table, membership audit, or rejection list is used.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Profile 7 -/

/-- The class-only skeleton of generated projector profile 7. -/
def a15MinedProjectorProfile07 : A15ProjectorProfile where
  centroidIndex := 7
  d := #[-30,
    -10, -10, -10, -10, -10, -10, -10, -10, -10,
    10, 10, 10, 30, 30, 30]
  reportedEligible := 169
  classValues := #[-30, -10, 10, 30]
  classSizes := #[1, 9, 3, 3]
  orbits := #[]

theorem a15MinedProjectorProfile07_centroidVector :
    a15MinedProjectorProfile07.centroidVector =
      a15SmallProfile a15MinedNormProfile07 := by
  funext i
  fin_cases i <;> rfl

private theorem a15MinedProjectorProfile07_static :
    (∑ i, a15MinedProjectorProfile07.centroidVector i) = 0 ∧
    (∀ i, a15MinedProjectorProfile07.classIndexCount i = 1) ∧
    (∀ c : Fin a15MinedProjectorProfile07.classSizes.size,
      (a15MinedProjectorProfile07.classFinset c.1).card =
        a15MinedProjectorProfile07.classSizes.getD c.1 0 ∧
      ∀ i, a15MinedProjectorProfile07.inClass c.1 i →
        a15MinedProjectorProfile07.centroidVector i =
          a15MinedProjectorProfile07.classValues.getD c.1 0) := by
  decide +kernel

private theorem a15MinedProjectorProfile07_countCases
    (s : A15EligibleIndex a15MinedProjectorProfile07.centroidVector) :
    let r0 := a15ProjectorClassCount
      a15MinedProjectorProfile07.classSizes (a15FourSubsetAt s.1) 0
    let r3 := a15ProjectorClassCount
      a15MinedProjectorProfile07.classSizes (a15FourSubsetAt s.1) 3
    (a15SubsetSum a15MinedProjectorProfile07.centroidVector s.1 = 60 →
        (r0 = 0 ∧ r3 = 1) ∨ (r0 = 0 ∧ r3 = 2) ∨
          (r0 = 1 ∧ r3 = 3)) ∧
      (a15SubsetSum a15MinedProjectorProfile07.centroidVector s.1 = -60 →
        r0 = 1 ∧ r3 = 0) := by
  let r0 := a15ProjectorClassCount
    a15MinedProjectorProfile07.classSizes (a15FourSubsetAt s.1) 0
  let r1 := a15ProjectorClassCount
    a15MinedProjectorProfile07.classSizes (a15FourSubsetAt s.1) 1
  let r2 := a15ProjectorClassCount
    a15MinedProjectorProfile07.classSizes (a15FourSubsetAt s.1) 2
  let r3 := a15ProjectorClassCount
    a15MinedProjectorProfile07.classSizes (a15FourSubsetAt s.1) 3
  have hsum := a15MinedProjectorProfile07.sum_classCounts
    a15MinedProjectorProfile07_static.2.1 s.1
  have hweighted := a15MinedProjectorProfile07.weighted_classCounts
    a15MinedProjectorProfile07_static.2.1
    (fun c => (a15MinedProjectorProfile07_static.2.2 c).2) s.1
  have h0 := a15MinedProjectorProfile07.classCount_le_classSize
    ⟨0, by decide⟩ s.1
      (a15MinedProjectorProfile07_static.2.2 ⟨0, by decide⟩).1
  have h1 := a15MinedProjectorProfile07.classCount_le_classSize
    ⟨1, by decide⟩ s.1
      (a15MinedProjectorProfile07_static.2.2 ⟨1, by decide⟩).1
  have h2 := a15MinedProjectorProfile07.classCount_le_classSize
    ⟨2, by decide⟩ s.1
      (a15MinedProjectorProfile07_static.2.2 ⟨2, by decide⟩).1
  have h3 := a15MinedProjectorProfile07.classCount_le_classSize
    ⟨3, by decide⟩ s.1
      (a15MinedProjectorProfile07_static.2.2 ⟨3, by decide⟩).1
  change (∑ c : Fin 4,
    a15ProjectorClassCount #[1, 9, 3, 3]
      (a15FourSubsetAt s.1) c.1) = 4 at hsum
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hsum
  norm_num at hsum
  change (∑ c : Fin 4,
    (#[(-30 : ℤ), -10, 10, 30].getD c.1 0 : ℤ) *
      a15ProjectorClassCount #[1, 9, 3, 3]
        (a15FourSubsetAt s.1) c.1) = _ at hweighted
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hweighted
  norm_num at hweighted
  norm_num [a15MinedProjectorProfile07] at h0 h1 h2 h3
  change
    (a15SubsetSum a15MinedProjectorProfile07.centroidVector s.1 = 60 →
        (a15ProjectorClassCount #[1, 9, 3, 3]
              (a15FourSubsetAt s.1) 0 = 0 ∧
            a15ProjectorClassCount #[1, 9, 3, 3]
              (a15FourSubsetAt s.1) 3 = 1) ∨
          (a15ProjectorClassCount #[1, 9, 3, 3]
              (a15FourSubsetAt s.1) 0 = 0 ∧
            a15ProjectorClassCount #[1, 9, 3, 3]
              (a15FourSubsetAt s.1) 3 = 2) ∨
          (a15ProjectorClassCount #[1, 9, 3, 3]
              (a15FourSubsetAt s.1) 0 = 1 ∧
            a15ProjectorClassCount #[1, 9, 3, 3]
              (a15FourSubsetAt s.1) 3 = 3)) ∧
      (a15SubsetSum a15MinedProjectorProfile07.centroidVector s.1 = -60 →
        a15ProjectorClassCount #[1, 9, 3, 3]
            (a15FourSubsetAt s.1) 0 = 1 ∧
          a15ProjectorClassCount #[1, 9, 3, 3]
            (a15FourSubsetAt s.1) 3 = 0)
  constructor <;> intro heligible <;> omega

private theorem a15MinedProjectorProfile07_pointwiseMoment
    (s : A15EligibleIndex a15MinedProjectorProfile07.centroidVector) :
    a15MinedProjectorProfile07.shellDifferenceMoment 3 s =
      96 + 32 *
        (∑ i ∈ a15MinedProjectorProfile07.classFinset 0,
          a15ProjectorShellCoordinate a15MinedProjectorProfile07.d
            (a15FourSubsetAt s.1) i) -
        192 * if a15ProjectorClassCount
          a15MinedProjectorProfile07.classSizes
            (a15FourSubsetAt s.1) 3 = 3 then 1 else 0 := by
  have hclass0 := a15MinedProjectorProfile07.sum_shellCoordinate_class s 0
  have hcases := a15MinedProjectorProfile07_countCases s
  rw [A15ProjectorProfile.shellDifferenceMoment_eq_card,
    ← a15ProjectorClassCount_eq_card]
  rw [hclass0, ← a15ProjectorClassCount_eq_card]
  rw [show (a15MinedProjectorProfile07.classFinset 3).card = 3 by decide,
    show (a15MinedProjectorProfile07.classFinset 0).card = 1 by decide]
  dsimp only at hcases
  rcases s.2 with hneg | hpos
  · have hsum :
        a15SubsetSum a15MinedProjectorProfile07.centroidVector s.1 = -60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hneg
    rcases hcases.2 hsum with ⟨hr0, hr3⟩
    simp [show a15SubsetSum
        a15MinedProjectorProfile07.centroidVector s.1 ≠ 60 by omega,
      hr0, hr3]
  · have hsum :
        a15SubsetSum a15MinedProjectorProfile07.centroidVector s.1 = 60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hpos
    rcases hcases.1 hsum with
      ⟨hr0, hr3⟩ | ⟨hr0, hr3⟩ | ⟨hr0, hr3⟩
    · simp [hsum, hr0, hr3]
    · simp [hsum, hr0, hr3]
    · simp [hsum, hr0, hr3]

private def a15MinedProjectorProfile07Exceptional :
    Finset (A15EligibleIndex a15MinedProjectorProfile07.centroidVector) :=
  Finset.univ.filter fun s =>
    a15ProjectorClassCount a15MinedProjectorProfile07.classSizes
      (a15FourSubsetAt s.1) 3 = 3

private theorem a15MinedProjectorProfile07Exceptional_card :
    a15MinedProjectorProfile07Exceptional.card = 1 := by
  let q : A15EligibleIndex a15MinedProjectorProfile07.centroidVector :=
    ⟨⟨454, by norm_num [a15FourSubsetData_size]⟩, by decide⟩
  have hextreme (s : A15EligibleIndex
      a15MinedProjectorProfile07.centroidVector)
      (hcount : a15ProjectorClassCount
        a15MinedProjectorProfile07.classSizes
          (a15FourSubsetAt s.1) 3 = 3) : s = q := by
    have hcases := a15MinedProjectorProfile07_countCases s
    dsimp only at hcases
    rcases s.2 with hneg | hpos
    · have hsum :
          a15SubsetSum a15MinedProjectorProfile07.centroidVector s.1 = -60 := by
        simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hneg
      have hr3 := (hcases.2 hsum).2
      omega
    · have hsum :
          a15SubsetSum a15MinedProjectorProfile07.centroidVector s.1 = 60 := by
        simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hpos
      rcases hcases.1 hsum with
        ⟨_hr0, hr3⟩ | ⟨_hr0, hr3⟩ | ⟨hr0, _hr3⟩
      · omega
      · omega
      · have hinter0 :
            (a15MinedProjectorProfile07.classFinset 0 ∩
              a15FourSubsetAsFinset s.1).card = 1 := by
          rw [← a15ProjectorClassCount_eq_card]
          exact hr0
        have hinter3 :
            (a15MinedProjectorProfile07.classFinset 3 ∩
              a15FourSubsetAsFinset s.1).card = 3 := by
          rw [← a15ProjectorClassCount_eq_card]
          exact hcount
        have hsubset0 : a15MinedProjectorProfile07.classFinset 0 ⊆
            a15FourSubsetAsFinset s.1 := by
          rw [← Finset.inter_eq_left]
          apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
          rw [hinter0]
          exact (a15MinedProjectorProfile07_static.2.2
            ⟨0, by decide⟩).1.le
        have hsubset3 : a15MinedProjectorProfile07.classFinset 3 ⊆
            a15FourSubsetAsFinset s.1 := by
          rw [← Finset.inter_eq_left]
          apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
          rw [hinter3]
          exact (a15MinedProjectorProfile07_static.2.2
            ⟨3, by decide⟩).1.le
        have hclasses :
            a15MinedProjectorProfile07.classFinset 0 ∪
                a15MinedProjectorProfile07.classFinset 3 =
              a15FourSubsetAsFinset q.1 := by
          decide
        have htargetSubset : a15FourSubsetAsFinset q.1 ⊆
            a15FourSubsetAsFinset s.1 := by
          rw [← hclasses]
          exact Finset.union_subset hsubset0 hsubset3
        have heq : a15FourSubsetAsFinset q.1 =
            a15FourSubsetAsFinset s.1 := by
          apply Finset.eq_of_subset_of_card_le htargetSubset
          rw [a15MinedFourSubsetAsFinset_card,
            a15MinedFourSubsetAsFinset_card]
        apply Subtype.ext
        exact a15FourSubsetAsFinset_injective heq.symm
  have hfinset : a15MinedProjectorProfile07Exceptional = {q} := by
    ext s
    simp only [a15MinedProjectorProfile07Exceptional,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact hextreme s
    · intro hs
      subst s
      decide
  rw [hfinset]
  simp

/-- Profile 7 has no direct A15 shell realization. -/
theorem a15MinedProjectorProfile07_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      a15MinedProjectorProfile07.centroidVector) : False := by
  let finite := realization.toFiniteShell G
  let exceptional := a15MinedProjectorProfile07Exceptional
  have htotal :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile07.centroidVector,
        (finite.multiplicity G s : ℤ)) = 220 := by
    rw [← Nat.cast_sum, finite.sum_multiplicity G,
      secondSubconstituent_card G hG x]
    norm_num
  have hclass0Total :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile07.centroidVector,
        (finite.multiplicity G s : ℤ) *
          (∑ i ∈ a15MinedProjectorProfile07.classFinset 0,
            a15ProjectorShellCoordinate a15MinedProjectorProfile07.d
              (a15FourSubsetAt s.1) i)) = -330 := by
    rw [realization.sum_multiplicity_shellClassSum G
      a15MinedProjectorProfile07 0]
    decide
  have hexceptional :
      (∑ s ∈ exceptional, (finite.multiplicity G s : ℤ)) ≤ 3 := by
    exact a15MinedExceptionalMultiplicity_le_three G hG x
      a15MinedProjectorProfile07 realization exceptional
      a15MinedProjectorProfile07Exceptional_card
  have hindicator :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile07.centroidVector,
        (finite.multiplicity G s : ℤ) *
          (if a15ProjectorClassCount a15MinedProjectorProfile07.classSizes
            (a15FourSubsetAt s.1) 3 = 3 then 1 else 0)) =
        ∑ s ∈ exceptional, (finite.multiplicity G s : ℤ) := by
    simp only [exceptional, a15MinedProjectorProfile07Exceptional,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_filter]
  have hmomentInt :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile07.centroidVector,
        (finite.multiplicity G s : ℤ) *
          a15MinedProjectorProfile07.shellDifferenceMoment 3 s) =
        10560 - 192 *
          (∑ s ∈ exceptional, (finite.multiplicity G s : ℤ)) := by
    simp_rw [a15MinedProjectorProfile07_pointwiseMoment]
    calc
      _ = 96 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile07.centroidVector,
            (finite.multiplicity G s : ℤ)) +
          32 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile07.centroidVector,
            (finite.multiplicity G s : ℤ) *
              (∑ i ∈ a15MinedProjectorProfile07.classFinset 0,
                a15ProjectorShellCoordinate a15MinedProjectorProfile07.d
                  (a15FourSubsetAt s.1) i)) -
          192 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile07.centroidVector,
            (finite.multiplicity G s : ℤ) *
              (if a15ProjectorClassCount
                a15MinedProjectorProfile07.classSizes
                  (a15FourSubsetAt s.1) 3 = 3 then 1 else 0)) := by
        calc
          _ = ∑ s : A15EligibleIndex
                a15MinedProjectorProfile07.centroidVector,
              (96 * (finite.multiplicity G s : ℤ) +
                32 * ((finite.multiplicity G s : ℤ) *
                  (∑ i ∈ a15MinedProjectorProfile07.classFinset 0,
                    a15ProjectorShellCoordinate a15MinedProjectorProfile07.d
                      (a15FourSubsetAt s.1) i)) -
                192 * ((finite.multiplicity G s : ℤ) *
                  (if a15ProjectorClassCount
                    a15MinedProjectorProfile07.classSizes
                      (a15FourSubsetAt s.1) 3 = 3 then 1 else 0))) := by
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by
        rw [htotal, hclass0Total, hindicator]
        ring
  have hmomentLowerInt :
      (9984 : ℤ) ≤
        ∑ s : A15EligibleIndex a15MinedProjectorProfile07.centroidVector,
          (finite.multiplicity G s : ℤ) *
            a15MinedProjectorProfile07.shellDifferenceMoment 3 s := by
    rw [hmomentInt]
    omega
  have hmomentLower :
      (9984 : ℚ) ≤
        ∑ s : A15EligibleIndex a15MinedProjectorProfile07.centroidVector,
          (finite.multiplicity G s : ℚ) *
            (a15MinedProjectorProfile07.shellDifferenceMoment 3 s : ℚ) := by
    exact_mod_cast hmomentLowerInt
  apply realization.no_realization_of_classMomentLowerBound
    G hG x a15MinedProjectorProfile07 ⟨3, by decide⟩
    a15MinedProjectorProfile07_static.1 (by decide)
    (a15MinedProjectorProfile07_static.2.2 ⟨3, by decide⟩).1
    (a15MinedProjectorProfile07_static.2.2 ⟨3, by decide⟩).2
    9984 hmomentLower
  norm_num [a15MinedProjectorProfile07]

/-- Mined norm profile 7 is the class-only profile 7 and is impossible. -/
theorem a15MinedNormProfile07_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      (a15SmallProfile a15MinedNormProfile07)) : False := by
  have hrealization : A15ShellGramRealization G x
      a15MinedProjectorProfile07.centroidVector :=
    a15MinedProjectorProfile07_centroidVector.symm ▸ realization
  exact a15MinedProjectorProfile07_no_realization G hG x hrealization

end SRG266
