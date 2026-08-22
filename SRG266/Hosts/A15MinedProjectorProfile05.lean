/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15MinedProjectorTheory
import SRG266.Hosts.A15MinedNormProfileData
import SRG266.Hosts.A15MinedSearch

/-!
# Mined exclusion of A15 projector profile 5

The certificate rejects four orbit-total candidates.  The relevant
three-coordinate class has
total difference moment

`10560 - 192 e`,

where `e` is the multiplicity of the unique extreme eligible four-subset.
Every shell multiplicity is at most three, so the moment is at least `9984`,
which already exceeds the positive-semidefinite projector pair budget.

The proof uses only class-count equations, the direct centroid equations, and
the general multiplicity bound.  It imports no orbit table, membership audit,
or rejection list.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem a15MinedExceptionalMultiplicity_le_three
    (hG : IsHypothetical G) (x : V)
    (profile : A15ProjectorProfile)
    (realization : A15ShellGramRealization G x profile.centroidVector)
    (exceptional : Finset (A15EligibleIndex profile.centroidVector))
    (hcard : exceptional.card = 1) :
    (∑ s ∈ exceptional,
      ((realization.toFiniteShell G).multiplicity G s : ℤ)) ≤ 3 := by
  let finite := realization.toFiniteShell G
  calc
    (∑ s ∈ exceptional, (finite.multiplicity G s : ℤ)) ≤
        ∑ _s ∈ exceptional, (3 : ℤ) := by
      apply Finset.sum_le_sum
      intro s hs
      exact_mod_cast finite.multiplicity_le_three G hG x s
    _ = exceptional.card * 3 := by simp
    _ = 3 := by rw [hcard]; norm_num

/-! ## Profile 5 -/

/-- The class-only skeleton of generated projector profile 5. -/
def a15MinedProjectorProfile05 : A15ProjectorProfile where
  centroidIndex := 5
  d := #[-30, -30, -30, -10, -10, -10,
    10, 10, 10, 10, 10, 10, 10, 10, 10, 30]
  reportedEligible := 169
  classValues := #[-30, -10, 10, 30]
  classSizes := #[3, 3, 9, 1]
  orbits := #[]

theorem a15MinedProjectorProfile05_centroidVector :
    a15MinedProjectorProfile05.centroidVector =
      a15SmallProfile a15MinedNormProfile09 := by
  funext i
  fin_cases i <;> rfl

private theorem a15MinedProjectorProfile05_static :
    (∑ i, a15MinedProjectorProfile05.centroidVector i) = 0 ∧
    (∀ i, a15MinedProjectorProfile05.classIndexCount i = 1) ∧
    (∀ c : Fin a15MinedProjectorProfile05.classSizes.size,
      (a15MinedProjectorProfile05.classFinset c.1).card =
        a15MinedProjectorProfile05.classSizes.getD c.1 0 ∧
      ∀ i, a15MinedProjectorProfile05.inClass c.1 i →
        a15MinedProjectorProfile05.centroidVector i =
          a15MinedProjectorProfile05.classValues.getD c.1 0) := by
  decide +kernel

private theorem a15MinedProjectorProfile05_countCases
    (s : A15EligibleIndex a15MinedProjectorProfile05.centroidVector) :
    let r0 := a15ProjectorClassCount
      a15MinedProjectorProfile05.classSizes (a15FourSubsetAt s.1) 0
    let r1 := a15ProjectorClassCount
      a15MinedProjectorProfile05.classSizes (a15FourSubsetAt s.1) 1
    let r2 := a15ProjectorClassCount
      a15MinedProjectorProfile05.classSizes (a15FourSubsetAt s.1) 2
    let r3 := a15ProjectorClassCount
      a15MinedProjectorProfile05.classSizes (a15FourSubsetAt s.1) 3
    (a15SubsetSum a15MinedProjectorProfile05.centroidVector s.1 = 60 →
        r0 = 0 ∧ r1 = 0) ∧
      (a15SubsetSum a15MinedProjectorProfile05.centroidVector s.1 = -60 →
        (r0 = 1 ∧ r1 = 3) ∨ (r0 = 2 ∧ r1 = 1) ∨
          (r0 = 3 ∧ r1 = 0 ∧ r2 = 0 ∧ r3 = 1)) := by
  let r0 := a15ProjectorClassCount
    a15MinedProjectorProfile05.classSizes (a15FourSubsetAt s.1) 0
  let r1 := a15ProjectorClassCount
    a15MinedProjectorProfile05.classSizes (a15FourSubsetAt s.1) 1
  let r2 := a15ProjectorClassCount
    a15MinedProjectorProfile05.classSizes (a15FourSubsetAt s.1) 2
  let r3 := a15ProjectorClassCount
    a15MinedProjectorProfile05.classSizes (a15FourSubsetAt s.1) 3
  have hsum := a15MinedProjectorProfile05.sum_classCounts
    a15MinedProjectorProfile05_static.2.1 s.1
  have hweighted := a15MinedProjectorProfile05.weighted_classCounts
    a15MinedProjectorProfile05_static.2.1
    (fun c => (a15MinedProjectorProfile05_static.2.2 c).2) s.1
  have h0 := a15MinedProjectorProfile05.classCount_le_classSize
    ⟨0, by decide⟩ s.1
      (a15MinedProjectorProfile05_static.2.2 ⟨0, by decide⟩).1
  have h1 := a15MinedProjectorProfile05.classCount_le_classSize
    ⟨1, by decide⟩ s.1
      (a15MinedProjectorProfile05_static.2.2 ⟨1, by decide⟩).1
  have h2 := a15MinedProjectorProfile05.classCount_le_classSize
    ⟨2, by decide⟩ s.1
      (a15MinedProjectorProfile05_static.2.2 ⟨2, by decide⟩).1
  have h3 := a15MinedProjectorProfile05.classCount_le_classSize
    ⟨3, by decide⟩ s.1
      (a15MinedProjectorProfile05_static.2.2 ⟨3, by decide⟩).1
  change (∑ c : Fin 4,
    a15ProjectorClassCount #[3, 3, 9, 1]
      (a15FourSubsetAt s.1) c.1) = 4 at hsum
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hsum
  norm_num at hsum
  change (∑ c : Fin 4,
    (#[(-30 : ℤ), -10, 10, 30].getD c.1 0 : ℤ) *
      a15ProjectorClassCount #[3, 3, 9, 1]
        (a15FourSubsetAt s.1) c.1) = _ at hweighted
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hweighted
  norm_num at hweighted
  norm_num [a15MinedProjectorProfile05] at h0 h1 h2 h3
  change
    (a15SubsetSum a15MinedProjectorProfile05.centroidVector s.1 = 60 →
        a15ProjectorClassCount #[3, 3, 9, 1]
            (a15FourSubsetAt s.1) 0 = 0 ∧
          a15ProjectorClassCount #[3, 3, 9, 1]
            (a15FourSubsetAt s.1) 1 = 0) ∧
      (a15SubsetSum a15MinedProjectorProfile05.centroidVector s.1 = -60 →
        (a15ProjectorClassCount #[3, 3, 9, 1]
              (a15FourSubsetAt s.1) 0 = 1 ∧
            a15ProjectorClassCount #[3, 3, 9, 1]
              (a15FourSubsetAt s.1) 1 = 3) ∨
          (a15ProjectorClassCount #[3, 3, 9, 1]
              (a15FourSubsetAt s.1) 0 = 2 ∧
            a15ProjectorClassCount #[3, 3, 9, 1]
              (a15FourSubsetAt s.1) 1 = 1) ∨
          (a15ProjectorClassCount #[3, 3, 9, 1]
              (a15FourSubsetAt s.1) 0 = 3 ∧
            a15ProjectorClassCount #[3, 3, 9, 1]
              (a15FourSubsetAt s.1) 1 = 0 ∧
            a15ProjectorClassCount #[3, 3, 9, 1]
              (a15FourSubsetAt s.1) 2 = 0 ∧
            a15ProjectorClassCount #[3, 3, 9, 1]
              (a15FourSubsetAt s.1) 3 = 1))
  constructor <;> intro heligible <;> omega

private theorem a15MinedProjectorProfile05_pointwiseMoment
    (s : A15EligibleIndex a15MinedProjectorProfile05.centroidVector) :
    a15MinedProjectorProfile05.shellDifferenceMoment 0 s =
      -288 - 64 *
        (∑ i ∈ a15MinedProjectorProfile05.classFinset 0,
          a15ProjectorShellCoordinate a15MinedProjectorProfile05.d
            (a15FourSubsetAt s.1) i) -
        32 *
        (∑ i ∈ a15MinedProjectorProfile05.classFinset 1,
          a15ProjectorShellCoordinate a15MinedProjectorProfile05.d
            (a15FourSubsetAt s.1) i) -
        192 * if a15ProjectorClassCount
          a15MinedProjectorProfile05.classSizes
            (a15FourSubsetAt s.1) 0 = 3 then 1 else 0 := by
  have hclass0 := a15MinedProjectorProfile05.sum_shellCoordinate_class s 0
  have hclass1 := a15MinedProjectorProfile05.sum_shellCoordinate_class s 1
  have hcases := a15MinedProjectorProfile05_countCases s
  rw [A15ProjectorProfile.shellDifferenceMoment_eq_card,
    ← a15ProjectorClassCount_eq_card]
  rw [hclass0, hclass1, ← a15ProjectorClassCount_eq_card,
    ← a15ProjectorClassCount_eq_card]
  rw [show (a15MinedProjectorProfile05.classFinset 0).card = 3 by decide,
    show (a15MinedProjectorProfile05.classFinset 1).card = 3 by decide]
  dsimp only at hcases
  rcases s.2 with hneg | hpos
  · have hsum :
        a15SubsetSum a15MinedProjectorProfile05.centroidVector s.1 = -60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hneg
    rcases hcases.2 hsum with
      ⟨hr0, hr1⟩ | ⟨hr0, hr1⟩ | ⟨hr0, hr1, _hr2, _hr3⟩
    · simp [show a15SubsetSum
          a15MinedProjectorProfile05.centroidVector s.1 ≠ 60 by omega,
        hr0, hr1]
    · simp [show a15SubsetSum
          a15MinedProjectorProfile05.centroidVector s.1 ≠ 60 by omega,
        hr0, hr1]
    · simp [show a15SubsetSum
          a15MinedProjectorProfile05.centroidVector s.1 ≠ 60 by omega,
        hr0, hr1]
  · have hsum :
        a15SubsetSum a15MinedProjectorProfile05.centroidVector s.1 = 60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hpos
    rcases hcases.1 hsum with ⟨hr0, hr1⟩
    simp [hsum, hr0, hr1]

private def a15MinedProjectorProfile05Exceptional :
    Finset (A15EligibleIndex a15MinedProjectorProfile05.centroidVector) :=
  Finset.univ.filter fun s =>
    a15ProjectorClassCount a15MinedProjectorProfile05.classSizes
      (a15FourSubsetAt s.1) 0 = 3

private theorem a15MinedProjectorProfile05Exceptional_card :
    a15MinedProjectorProfile05Exceptional.card = 1 := by
  let q : A15EligibleIndex a15MinedProjectorProfile05.centroidVector :=
    ⟨⟨12, by norm_num [a15FourSubsetData_size]⟩, by decide⟩
  have hextreme (s : A15EligibleIndex
      a15MinedProjectorProfile05.centroidVector)
      (hcount : a15ProjectorClassCount
        a15MinedProjectorProfile05.classSizes
          (a15FourSubsetAt s.1) 0 = 3) : s = q := by
    have hcases := a15MinedProjectorProfile05_countCases s
    dsimp only at hcases
    rcases s.2 with hneg | hpos
    · have hsum :
          a15SubsetSum a15MinedProjectorProfile05.centroidVector s.1 = -60 := by
        simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hneg
      rcases hcases.2 hsum with
        ⟨hr0, _⟩ | ⟨hr0, _⟩ | ⟨_hr0, _hr1, hr2, hr3⟩
      · omega
      · omega
      · have hinter0 :
            (a15MinedProjectorProfile05.classFinset 0 ∩
              a15FourSubsetAsFinset s.1).card = 3 := by
          rw [← a15ProjectorClassCount_eq_card]
          exact hcount
        have hinter3 :
            (a15MinedProjectorProfile05.classFinset 3 ∩
              a15FourSubsetAsFinset s.1).card = 1 := by
          rw [← a15ProjectorClassCount_eq_card]
          exact hr3
        have hsubset0 : a15MinedProjectorProfile05.classFinset 0 ⊆
            a15FourSubsetAsFinset s.1 := by
          rw [← Finset.inter_eq_left]
          apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
          rw [hinter0]
          exact (a15MinedProjectorProfile05_static.2.2
            ⟨0, by decide⟩).1.le
        have hsubset3 : a15MinedProjectorProfile05.classFinset 3 ⊆
            a15FourSubsetAsFinset s.1 := by
          rw [← Finset.inter_eq_left]
          apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
          rw [hinter3]
          exact (a15MinedProjectorProfile05_static.2.2
            ⟨3, by decide⟩).1.le
        have hclasses :
            a15MinedProjectorProfile05.classFinset 0 ∪
                a15MinedProjectorProfile05.classFinset 3 =
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
    · have hsum :
          a15SubsetSum a15MinedProjectorProfile05.centroidVector s.1 = 60 := by
        simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hpos
      have hr0 := (hcases.1 hsum).1
      omega
  have hfinset : a15MinedProjectorProfile05Exceptional = {q} := by
    ext s
    simp only [a15MinedProjectorProfile05Exceptional,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact hextreme s
    · intro hs
      subst s
      decide
  rw [hfinset]
  simp

/-- Profile 5 has no direct A15 shell realization. -/
theorem a15MinedProjectorProfile05_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      a15MinedProjectorProfile05.centroidVector) : False := by
  let finite := realization.toFiniteShell G
  let exceptional := a15MinedProjectorProfile05Exceptional
  have htotal :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile05.centroidVector,
        (finite.multiplicity G s : ℤ)) = 220 := by
    rw [← Nat.cast_sum, finite.sum_multiplicity G,
      secondSubconstituent_card G hG x]
    norm_num
  have hclass0Total :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile05.centroidVector,
        (finite.multiplicity G s : ℤ) *
          (∑ i ∈ a15MinedProjectorProfile05.classFinset 0,
            a15ProjectorShellCoordinate a15MinedProjectorProfile05.d
              (a15FourSubsetAt s.1) i)) = -990 := by
    rw [realization.sum_multiplicity_shellClassSum G
      a15MinedProjectorProfile05 0]
    decide
  have hclass1Total :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile05.centroidVector,
        (finite.multiplicity G s : ℤ) *
          (∑ i ∈ a15MinedProjectorProfile05.classFinset 1,
            a15ProjectorShellCoordinate a15MinedProjectorProfile05.d
              (a15FourSubsetAt s.1) i)) = -330 := by
    rw [realization.sum_multiplicity_shellClassSum G
      a15MinedProjectorProfile05 1]
    decide
  have hexceptional :
      (∑ s ∈ exceptional, (finite.multiplicity G s : ℤ)) ≤ 3 := by
    exact a15MinedExceptionalMultiplicity_le_three G hG x
      a15MinedProjectorProfile05 realization exceptional
      a15MinedProjectorProfile05Exceptional_card
  have hindicator :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile05.centroidVector,
        (finite.multiplicity G s : ℤ) *
          (if a15ProjectorClassCount a15MinedProjectorProfile05.classSizes
            (a15FourSubsetAt s.1) 0 = 3 then 1 else 0)) =
        ∑ s ∈ exceptional, (finite.multiplicity G s : ℤ) := by
    simp only [exceptional, a15MinedProjectorProfile05Exceptional,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_filter]
  have hmomentInt :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile05.centroidVector,
        (finite.multiplicity G s : ℤ) *
          a15MinedProjectorProfile05.shellDifferenceMoment 0 s) =
        10560 - 192 *
          (∑ s ∈ exceptional, (finite.multiplicity G s : ℤ)) := by
    simp_rw [a15MinedProjectorProfile05_pointwiseMoment]
    calc
      _ = -288 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile05.centroidVector,
            (finite.multiplicity G s : ℤ)) -
          64 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile05.centroidVector,
            (finite.multiplicity G s : ℤ) *
              (∑ i ∈ a15MinedProjectorProfile05.classFinset 0,
                a15ProjectorShellCoordinate a15MinedProjectorProfile05.d
                  (a15FourSubsetAt s.1) i)) -
          32 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile05.centroidVector,
            (finite.multiplicity G s : ℤ) *
              (∑ i ∈ a15MinedProjectorProfile05.classFinset 1,
                a15ProjectorShellCoordinate a15MinedProjectorProfile05.d
                  (a15FourSubsetAt s.1) i)) -
          192 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile05.centroidVector,
            (finite.multiplicity G s : ℤ) *
              (if a15ProjectorClassCount
                a15MinedProjectorProfile05.classSizes
                  (a15FourSubsetAt s.1) 0 = 3 then 1 else 0)) := by
        calc
          _ = ∑ s : A15EligibleIndex
                a15MinedProjectorProfile05.centroidVector,
              (-288 * (finite.multiplicity G s : ℤ) -
                64 * ((finite.multiplicity G s : ℤ) *
                  (∑ i ∈ a15MinedProjectorProfile05.classFinset 0,
                    a15ProjectorShellCoordinate a15MinedProjectorProfile05.d
                      (a15FourSubsetAt s.1) i)) -
                32 * ((finite.multiplicity G s : ℤ) *
                  (∑ i ∈ a15MinedProjectorProfile05.classFinset 1,
                    a15ProjectorShellCoordinate a15MinedProjectorProfile05.d
                      (a15FourSubsetAt s.1) i)) -
                192 * ((finite.multiplicity G s : ℤ) *
                  (if a15ProjectorClassCount
                    a15MinedProjectorProfile05.classSizes
                      (a15FourSubsetAt s.1) 0 = 3 then 1 else 0))) := by
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              Finset.sum_sub_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by
        rw [htotal, hclass0Total, hclass1Total, hindicator]
        ring
  have hmomentLowerInt :
      (9984 : ℤ) ≤
        ∑ s : A15EligibleIndex a15MinedProjectorProfile05.centroidVector,
          (finite.multiplicity G s : ℤ) *
            a15MinedProjectorProfile05.shellDifferenceMoment 0 s := by
    rw [hmomentInt]
    omega
  have hmomentLower :
      (9984 : ℚ) ≤
        ∑ s : A15EligibleIndex a15MinedProjectorProfile05.centroidVector,
          (finite.multiplicity G s : ℚ) *
            (a15MinedProjectorProfile05.shellDifferenceMoment 0 s : ℚ) := by
    exact_mod_cast hmomentLowerInt
  apply realization.no_realization_of_classMomentLowerBound
    G hG x a15MinedProjectorProfile05 ⟨0, by decide⟩
    a15MinedProjectorProfile05_static.1 (by decide)
    (a15MinedProjectorProfile05_static.2.2 ⟨0, by decide⟩).1
    (a15MinedProjectorProfile05_static.2.2 ⟨0, by decide⟩).2
    9984 hmomentLower
  norm_num [a15MinedProjectorProfile05]

/-- Mined norm profile 9 is the class-only profile 5 and is impossible. -/
theorem a15MinedNormProfile09_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      (a15SmallProfile a15MinedNormProfile09)) : False := by
  have hrealization : A15ShellGramRealization G x
      a15MinedProjectorProfile05.centroidVector :=
    a15MinedProjectorProfile05_centroidVector.symm ▸ realization
  exact a15MinedProjectorProfile05_no_realization G hG x hrealization

end SRG266
