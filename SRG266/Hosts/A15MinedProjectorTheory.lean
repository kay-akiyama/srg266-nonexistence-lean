/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15ProjectorSoundnessTheory
import SRG266.Hosts.A15QuickBridge

/-!
# Compact class-count theory for the mined A15 profiles

The generated projector profiles store full first and second orbit moments.
The mined exclusion path needs only the coordinate classes and the numbers of
selected coordinates in those classes.  This module derives the universal
count and weighted-sum equations directly from the four-subset model.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000

theorem a15MinedFourSubsetAsFinset_card (s : A15FourSubsetIndex) :
    (a15FourSubsetAsFinset s).card = 4 := by
  unfold a15FourSubsetAsFinset A15FourSubset.asFinset
  rw [List.toFinset_card_of_nodup
    (a15FourSubsetAt_coordinates_nodup s)]
  rfl

theorem A15ProjectorProfile.classCount_le_classSize
    (profile : A15ProjectorProfile)
    (c : Fin profile.classSizes.size) (s : A15FourSubsetIndex)
    (hcard : (profile.classFinset c.1).card =
      profile.classSizes.getD c.1 0) :
    a15ProjectorClassCount profile.classSizes
        (a15FourSubsetAt s) c.1 ≤
      profile.classSizes.getD c.1 0 := by
  rw [a15ProjectorClassCount_eq_card, ← hcard]
  exact Finset.card_le_card (Finset.inter_subset_left)

private theorem A15ProjectorProfile.classCount_eq_indicatorSum
    (profile : A15ProjectorProfile)
    (c : Fin profile.classSizes.size) (s : A15FourSubsetIndex) :
    a15ProjectorClassCount profile.classSizes
        (a15FourSubsetAt s) c.1 =
      ∑ i ∈ a15FourSubsetAsFinset s,
        if profile.inClass c.1 i then 1 else 0 := by
  rw [a15ProjectorClassCount_eq_card]
  have hinter :
      profile.classFinset c.1 ∩ a15FourSubsetAsFinset s =
        (a15FourSubsetAsFinset s).filter (profile.inClass c.1) := by
    ext i
    simp [A15ProjectorProfile.classFinset, and_comm]
  rw [hinter, Finset.card_filter]

theorem A15ProjectorProfile.sum_classCounts
    (profile : A15ProjectorProfile)
    (hunique : ∀ i, profile.classIndexCount i = 1)
    (s : A15FourSubsetIndex) :
    (∑ c : Fin profile.classSizes.size,
      a15ProjectorClassCount profile.classSizes
        (a15FourSubsetAt s) c.1) = 4 := by
  simp_rw [profile.classCount_eq_indicatorSum]
  rw [Finset.sum_comm]
  calc
    (∑ i ∈ a15FourSubsetAsFinset s,
      ∑ c : Fin profile.classSizes.size,
        if profile.inClass c.1 i then 1 else 0) =
        ∑ _i ∈ a15FourSubsetAsFinset s, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiUnique := hunique i
      unfold A15ProjectorProfile.classIndexCount at hiUnique
      rw [Finset.card_filter] at hiUnique
      exact hiUnique
    _ = 4 := by simp [a15MinedFourSubsetAsFinset_card]

theorem A15ProjectorProfile.weighted_classCounts
    (profile : A15ProjectorProfile)
    (hunique : ∀ i, profile.classIndexCount i = 1)
    (hclass : ∀ c : Fin profile.classSizes.size,
      ∀ i, profile.inClass c.1 i →
        profile.centroidVector i = profile.classValues.getD c.1 0)
    (s : A15FourSubsetIndex) :
    (∑ c : Fin profile.classSizes.size,
      (profile.classValues.getD c.1 0 : ℤ) *
        a15ProjectorClassCount profile.classSizes
          (a15FourSubsetAt s) c.1) =
      a15SubsetSum profile.centroidVector s := by
  have hcount (c : Fin profile.classSizes.size) :
      (a15ProjectorClassCount profile.classSizes
          (a15FourSubsetAt s) c.1 : ℤ) =
        ∑ i ∈ a15FourSubsetAsFinset s,
          if profile.inClass c.1 i then (1 : ℤ) else 0 := by
    exact_mod_cast profile.classCount_eq_indicatorSum c s
  simp_rw [hcount]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hpoint (i : Fin 16) :
      (∑ c : Fin profile.classSizes.size,
        (profile.classValues.getD c.1 0 : ℤ) *
          if profile.inClass c.1 i then 1 else 0) =
        profile.centroidVector i := by
    have honeNat :
        (∑ c : Fin profile.classSizes.size,
          if profile.inClass c.1 i then 1 else 0) = 1 := by
      have hiUnique := hunique i
      unfold A15ProjectorProfile.classIndexCount at hiUnique
      rw [Finset.card_filter] at hiUnique
      exact hiUnique
    have hone :
        (∑ c : Fin profile.classSizes.size,
          if profile.inClass c.1 i then (1 : ℤ) else 0) = 1 := by
      exact_mod_cast honeNat
    calc
      _ = ∑ c : Fin profile.classSizes.size,
          if profile.inClass c.1 i then
            profile.classValues.getD c.1 0 else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hci : profile.inClass c.1 i <;> simp [hci]
      _ = ∑ c : Fin profile.classSizes.size,
          if profile.inClass c.1 i then
            profile.centroidVector i else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hci : profile.inClass c.1 i
        · simp [hci, hclass c i hci]
        · simp [hci]
      _ = (∑ c : Fin profile.classSizes.size,
          if profile.inClass c.1 i then (1 : ℤ) else 0) *
            profile.centroidVector i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hci : profile.inClass c.1 i <;> simp [hci]
      _ = profile.centroidVector i := by rw [hone]; simp
  calc
    (∑ i ∈ a15FourSubsetAsFinset s,
      ∑ c : Fin profile.classSizes.size,
        (profile.classValues.getD c.1 0 : ℤ) *
          if profile.inClass c.1 i then 1 else 0) =
        ∑ i ∈ a15FourSubsetAsFinset s,
          profile.centroidVector i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = a15SubsetSum profile.centroidVector s := by
      exact (a15FourSubset_valueSum_eq_finset_sum
        profile.centroidVector s).symm

/-- Sum of the signed shell coordinates over one coordinate class, expressed
only through the class size and its four-subset intersection count. -/
theorem A15ProjectorProfile.sum_shellCoordinate_class
    (profile : A15ProjectorProfile)
    (s : A15EligibleIndex profile.centroidVector) (c : ℕ) :
    (∑ i ∈ profile.classFinset c,
      a15ProjectorShellCoordinate profile.d
        (a15FourSubsetAt s.1) i) =
      if a15SubsetSum profile.centroidVector s.1 = 60 then
        -((profile.classFinset c).card -
          4 * (profile.classFinset c ∩
            a15FourSubsetAsFinset s.1).card : ℤ)
      else
        ((profile.classFinset c).card -
          4 * (profile.classFinset c ∩
            a15FourSubsetAsFinset s.1).card : ℤ) := by
  simp_rw [a15ProjectorShellCoordinate_eq_shellVector4 profile s]
  unfold a15ShellVector4 a15ShellCoordinate4
  by_cases hsum : a15SubsetSum profile.centroidVector s.1 = 60
  · simp only [hsum, if_true, Finset.sum_neg_distrib]
    simpa [a15SignedCoordinate] using
      congrArg Neg.neg
        (a15_signed_sum (profile.classFinset c)
          (a15FourSubsetAsFinset s.1))
  · simp only [hsum, if_false]
    simpa [a15SignedCoordinate] using
      a15_signed_sum (profile.classFinset c)
        (a15FourSubsetAsFinset s.1)

/-- The base complement bilinear form on two class indicators depends only
on their intersection, cardinalities, and centroid sums. -/
theorem A15ProjectorProfile.baseQForm_classIndicators
    (profile : A15ProjectorProfile) (c e : ℕ) :
    profile.baseQForm (a15ClassIndicator profile c)
        (a15ClassIndicator profile e) =
      ((profile.classFinset c ∩ profile.classFinset e).card : ℚ) -
        ((profile.classFinset c).card : ℚ) *
          ((profile.classFinset e).card : ℚ) / 16 +
        ((∑ i ∈ profile.classFinset c,
          (profile.centroidVector i : ℚ)) *
        (∑ j ∈ profile.classFinset e,
          (profile.centroidVector j : ℚ))) / 1800 := by
  unfold A15ProjectorProfile.baseQForm a15ClassIndicator
  simp_rw [a15_getD_ofFn]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul,
    one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  calc
    (∑ i : Fin 16, ∑ j : Fin 16,
      if profile.inClass e j then
        if profile.inClass c i then profile.baseEntry i j else 0
      else 0) =
        ∑ i ∈ profile.classFinset c,
          ∑ j ∈ profile.classFinset e, profile.baseEntry i j := by
      symm
      unfold A15ProjectorProfile.classFinset
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_filter]
      by_cases hi : profile.inClass c i <;> simp [hi]
    _ = _ := by
      unfold A15ProjectorProfile.baseEntry
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hproduct :
          (∑ x ∈ profile.classFinset c,
            ∑ y ∈ profile.classFinset e,
              (profile.d.getD x.1 0 : ℚ) *
                (profile.d.getD y.1 0 : ℚ) / 1800) =
            ((∑ x ∈ profile.classFinset c,
              (profile.d.getD x.1 0 : ℚ)) *
            (∑ y ∈ profile.classFinset e,
              (profile.d.getD y.1 0 : ℚ))) / 1800 := by
        calc
          _ = ∑ x ∈ profile.classFinset c,
              ((profile.d.getD x.1 0 : ℚ) *
                (∑ y ∈ profile.classFinset e,
                  (profile.d.getD y.1 0 : ℚ))) / 1800 := by
            apply Finset.sum_congr rfl
            intro x _
            calc
              _ = ∑ y ∈ profile.classFinset e,
                  ((profile.d.getD x.1 0 : ℚ) / 1800) *
                    (profile.d.getD y.1 0 : ℚ) := by
                apply Finset.sum_congr rfl
                intro y _
                ring
              _ = ((profile.d.getD x.1 0 : ℚ) / 1800) *
                  (∑ y ∈ profile.classFinset e,
                    (profile.d.getD y.1 0 : ℚ)) := by
                rw [Finset.mul_sum]
              _ = _ := by ring
          _ = ∑ x ∈ profile.classFinset c,
              (profile.d.getD x.1 0 : ℚ) *
                ((∑ y ∈ profile.classFinset e,
                  (profile.d.getD y.1 0 : ℚ)) / 1800) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
          _ = (∑ x ∈ profile.classFinset c,
                (profile.d.getD x.1 0 : ℚ)) *
              ((∑ y ∈ profile.classFinset e,
                (profile.d.getD y.1 0 : ℚ)) / 1800) := by
            rw [Finset.sum_mul]
          _ = _ := by ring
      rw [hproduct]
      simp [A15ProjectorProfile.centroidVector]
      ring

/-- The base complement form on a coordinate-class indicator depends only on
the class cardinality and its centroid sum. -/
theorem A15ProjectorProfile.baseQForm_classIndicator
    (profile : A15ProjectorProfile) (c : ℕ) :
    profile.baseQForm (a15ClassIndicator profile c)
        (a15ClassIndicator profile c) =
      ((profile.classFinset c).card : ℚ) -
        ((profile.classFinset c).card : ℚ) ^ 2 / 16 +
        ((∑ i ∈ profile.classFinset c,
          (profile.centroidVector i : ℚ)) ^ 2) / 1800 := by
  unfold A15ProjectorProfile.baseQForm a15ClassIndicator
  simp_rw [a15_getD_ofFn]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul,
    one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  calc
    (∑ i : Fin 16, ∑ j : Fin 16,
      if profile.inClass c j then
        if profile.inClass c i then profile.baseEntry i j else 0
      else 0) =
        ∑ i ∈ profile.classFinset c,
          ∑ j ∈ profile.classFinset c, profile.baseEntry i j := by
      symm
      unfold A15ProjectorProfile.classFinset
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_filter]
      by_cases hi : profile.inClass c i <;> simp [hi]
    _ = _ := by
      unfold A15ProjectorProfile.baseEntry
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hproduct :
          (∑ x ∈ profile.classFinset c,
            ∑ y ∈ profile.classFinset c,
              (profile.d.getD x.1 0 : ℚ) *
                (profile.d.getD y.1 0 : ℚ) / 1800) =
            (∑ x ∈ profile.classFinset c,
              (profile.d.getD x.1 0 : ℚ)) ^ 2 / 1800 := by
        calc
          _ = ∑ x ∈ profile.classFinset c,
              ((profile.d.getD x.1 0 : ℚ) *
                (∑ y ∈ profile.classFinset c,
                  (profile.d.getD y.1 0 : ℚ))) / 1800 := by
            apply Finset.sum_congr rfl
            intro x _
            calc
              _ = ∑ y ∈ profile.classFinset c,
                  ((profile.d.getD x.1 0 : ℚ) / 1800) *
                    (profile.d.getD y.1 0 : ℚ) := by
                apply Finset.sum_congr rfl
                intro y _
                ring
              _ = ((profile.d.getD x.1 0 : ℚ) / 1800) *
                  (∑ y ∈ profile.classFinset c,
                    (profile.d.getD y.1 0 : ℚ)) := by
                rw [Finset.mul_sum]
              _ = _ := by ring
          _ = ∑ x ∈ profile.classFinset c,
              (profile.d.getD x.1 0 : ℚ) *
                ((∑ y ∈ profile.classFinset c,
                  (profile.d.getD y.1 0 : ℚ)) / 1800) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
          _ = (∑ x ∈ profile.classFinset c,
                (profile.d.getD x.1 0 : ℚ)) *
              ((∑ y ∈ profile.classFinset c,
                (profile.d.getD y.1 0 : ℚ)) / 1800) := by
            rw [Finset.sum_mul]
          _ = _ := by ring
      rw [hproduct]
      simp [A15ProjectorProfile.centroidVector]
      ring

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The realization centroid equation, summed over an arbitrary coordinate
class.  This avoids rebuilding orbit first-moment tables. -/
theorem A15ShellGramRealization.sum_multiplicity_shellClassSum
    {x : V}
    (profile : A15ProjectorProfile)
    (realization : A15ShellGramRealization G x profile.centroidVector)
    (c : ℕ) :
    (∑ s : A15EligibleIndex profile.centroidVector,
      ((realization.toFiniteShell G).multiplicity G s : ℤ) *
        (∑ i ∈ profile.classFinset c,
          a15ProjectorShellCoordinate profile.d
            (a15FourSubsetAt s.1) i)) =
      ∑ i ∈ profile.classFinset c,
        11 * profile.centroidVector i := by
  let finite := realization.toFiniteShell G
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ s : A15EligibleIndex profile.centroidVector,
      (finite.multiplicity G s : ℤ) *
        a15ProjectorShellCoordinate profile.d
          (a15FourSubsetAt s.1) i) =
        ∑ s : A15EligibleIndex profile.centroidVector,
          (finite.multiplicity G s : ℤ) *
            a15ShellVector4 profile.centroidVector s i := by
      apply Finset.sum_congr rfl
      intro s _
      rw [a15ProjectorShellCoordinate_eq_shellVector4]
    _ = ∑ B, a15ShellVector4 profile.centroidVector
        (realization.shell B) i := by
      exact finite.sum_multiplicity_mul G
        (fun s => a15ShellVector4 profile.centroidVector s i)
    _ = 11 * profile.centroidVector i := realization.centroid i

/-- A lower bound on one total class-difference moment that exceeds the
projector pair budget excludes a direct shell realization. -/
theorem A15ShellGramRealization.no_realization_of_classMomentLowerBound
    (hG : IsHypothetical G) (x : V)
    (profile : A15ProjectorProfile)
    (realization : A15ShellGramRealization G x profile.centroidVector)
    (c : Fin profile.classSizes.size)
    (hdSum : ∑ i, profile.centroidVector i = 0)
    (hnpos : 0 < profile.classSizes.getD c.1 0)
    (hcard : (profile.classFinset c.1).card =
      profile.classSizes.getD c.1 0)
    (hclass : ∀ i, profile.inClass c.1 i →
      profile.centroidVector i = profile.classValues.getD c.1 0)
    (momentLower : ℚ)
    (hmomentLower : momentLower ≤
      ∑ s : A15EligibleIndex profile.centroidVector,
        ((realization.toFiniteShell G).multiplicity G s : ℚ) *
          (profile.shellDifferenceMoment c.1 s : ℚ))
    (hnegative :
      2 * ((profile.classSizes.getD c.1 0 : ℚ) *
        ((profile.classSizes.getD c.1 0 : ℚ) - 1)) -
        momentLower / 720 < 0) : False := by
  have hnonneg :=
    realization.standardDifferenceQSum_nonneg_of_sum_zero
      G hG x profile hdSum c.1
  have hformula :=
    realization.standardDifferenceQSum_eq_shellMoment
      G profile c hnpos hcard hclass
  rw [hformula] at hnonneg
  linarith

/-- An exact total class-difference moment that exceeds the projector pair
budget excludes a direct shell realization. -/
theorem A15ShellGramRealization.no_realization_of_classMomentSum
    (hG : IsHypothetical G) (x : V)
    (profile : A15ProjectorProfile)
    (realization : A15ShellGramRealization G x profile.centroidVector)
    (c : Fin profile.classSizes.size)
    (hdSum : ∑ i, profile.centroidVector i = 0)
    (hnpos : 0 < profile.classSizes.getD c.1 0)
    (hcard : (profile.classFinset c.1).card =
      profile.classSizes.getD c.1 0)
    (hclass : ∀ i, profile.inClass c.1 i →
      profile.centroidVector i = profile.classValues.getD c.1 0)
    (momentSum : ℚ)
    (hmomentSum :
      (∑ s : A15EligibleIndex profile.centroidVector,
        ((realization.toFiniteShell G).multiplicity G s : ℚ) *
          (profile.shellDifferenceMoment c.1 s : ℚ)) = momentSum)
    (hnegative :
      2 * ((profile.classSizes.getD c.1 0 : ℚ) *
        ((profile.classSizes.getD c.1 0 : ℚ) - 1)) -
        momentSum / 720 < 0) : False := by
  have hnonneg :=
    realization.standardDifferenceQSum_nonneg_of_sum_zero
      G hG x profile hdSum c.1
  have hformula :=
    realization.standardDifferenceQSum_eq_shellMoment
      G profile c hnpos hcard hclass
  rw [hformula, hmomentSum] at hnonneg
  linarith

/-- A constant class-difference moment that exceeds the projector pair budget
excludes a direct shell realization. -/
theorem A15ShellGramRealization.no_realization_of_constant_classMoment
    (hG : IsHypothetical G) (x : V)
    (profile : A15ProjectorProfile)
    (realization : A15ShellGramRealization G x profile.centroidVector)
    (c : Fin profile.classSizes.size)
    (hdSum : ∑ i, profile.centroidVector i = 0)
    (hnpos : 0 < profile.classSizes.getD c.1 0)
    (hcard : (profile.classFinset c.1).card =
      profile.classSizes.getD c.1 0)
    (hclass : ∀ i, profile.inClass c.1 i →
      profile.centroidVector i = profile.classValues.getD c.1 0)
    (moment : ℤ)
    (hmoment : ∀ s : A15EligibleIndex profile.centroidVector,
      profile.shellDifferenceMoment c.1 s = moment)
    (hnegative :
      2 * ((profile.classSizes.getD c.1 0 : ℚ) *
        ((profile.classSizes.getD c.1 0 : ℚ) - 1)) -
        (220 * (moment : ℚ)) / 720 < 0) : False := by
  have hmomentSum :
      (∑ s : A15EligibleIndex profile.centroidVector,
        ((realization.toFiniteShell G).multiplicity G s : ℚ) *
          (profile.shellDifferenceMoment c.1 s : ℚ)) =
        220 * moment := by
    simp_rw [hmoment]
    rw [← Finset.sum_mul, ← Nat.cast_sum,
      (realization.toFiniteShell G).sum_multiplicity G,
      secondSubconstituent_card G hG x]
    norm_num
  exact realization.no_realization_of_classMomentSum G hG x profile c
    hdSum hnpos hcard hclass (220 * moment) hmomentSum hnegative

end SRG266
