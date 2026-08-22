/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15MagnitudeExtraction
import SRG266.Certificates.E7MinedNormOutput
import Mathlib.Data.List.GetD

/-!
# The mined small E7 component search

After the lattice congruence divides an E7 half-block by five, the eight
coordinates have sum zero, common parity, and squared norm in
`{8, 16, 24, 32, 40}`.  This file computes that search directly by signed
magnitudes at most six.  Its output has only 25 canonical profiles.
-/

namespace SRG266

set_option maxRecDepth 100000

def e7SmallNormCase (sq : ℕ) : Bool :=
  decide (sq = 8 ∨ sq = 16 ∨ sq = 24 ∨ sq = 32 ∨ sq = 40)

def e7SmallCommonParity (coordinates : List ℤ) : Bool :=
  coordinates.all fun z => z % 2 = coordinates.getD 0 0 % 2

theorem e7SmallCommonParity_of_mod_eq
    (coordinates : List ℤ) (p : ℤ)
    (hall : ∀ z ∈ coordinates, z % 2 = p)
    (hzero : coordinates.getD 0 0 % 2 = p) :
    e7SmallCommonParity coordinates = true := by
  unfold e7SmallCommonParity
  apply List.all_eq_true.mpr
  intro z hz
  simpa only [decide_eq_true_eq, hall z hz] using hzero.symm

/-- Necessary pruning for a remaining signed-magnitude path. -/
def e7SmallMagnitudeFeasible
    (m remaining : ℕ) (newSum : ℤ) (newSq : ℕ) : Bool :=
  let nextMagnitude := m - 1
  decide (
    newSq ≤ 40 ∧
    newSum.natAbs ≤ remaining * nextMagnitude)

/-- Canonical eight-coordinate recursion after division by five. -/
def e7SmallEnumerateByMagnitudeAux :
    (m remaining : ℕ) → (sum : ℤ) → (sq : ℕ) →
      List ℤ → List ℤ → List (List ℤ)
  | 0, remaining, sum, sq, negatives, positives =>
      if sum = 0 && e7SmallNormCase sq then
        let coordinates :=
          negatives ++ List.replicate remaining 0 ++ positives
        if e7SmallCommonParity coordinates then [coordinates] else []
      else
        []
  | m + 1, remaining, sum, sq, negatives, positives =>
      (List.range (remaining + 1)).flatMap fun negativeCount =>
        (List.range (remaining - negativeCount + 1)).flatMap fun positiveCount =>
          let used := negativeCount + positiveCount
          let newRemaining := remaining - used
          let signedMultiplicity : ℤ :=
            (positiveCount : ℤ) - negativeCount
          let newSum := sum + signedMultiplicity * (m + 1)
          let newSq := sq + used * (m + 1) ^ 2
          if e7SmallMagnitudeFeasible (m + 1) newRemaining newSum newSq then
            e7SmallEnumerateByMagnitudeAux m newRemaining newSum newSq
              (negatives ++
                List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
              (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++ positives)
          else
            []

def e7SmallNormProfiles : List (List ℤ) :=
  e7SmallEnumerateByMagnitudeAux 6 8 0 0 [] []

/-- Every exact small magnitude path survives the pruning tests. -/
theorem e7SmallEnumerateByMagnitudeAux_contains_of_choices
    (choices : List (ℕ × ℕ)) (targetSq : ℕ)
    (htargetSq :
      targetSq = 8 ∨ targetSq = 16 ∨ targetSq = 24 ∨
        targetSq = 32 ∨ targetSq = 40)
    (remaining : ℕ) (sum : ℤ) (sq zeroCount : ℕ)
    (negatives positives : List ℤ)
    (hcount :
      a15MagnitudeChoiceUsed choices + zeroCount = remaining)
    (hsum : sum + a15MagnitudeChoiceSum choices = 0)
    (hsq : sq + a15MagnitudeChoiceSq choices = targetSq)
    (hparity :
      e7SmallCommonParity
        (negatives ++ a15MagnitudeChoiceNegatives choices ++
          List.replicate zeroCount 0 ++
          a15MagnitudeChoicePositives choices ++ positives) = true) :
    negatives ++ a15MagnitudeChoiceNegatives choices ++
        List.replicate zeroCount 0 ++
        a15MagnitudeChoicePositives choices ++ positives ∈
      e7SmallEnumerateByMagnitudeAux choices.length remaining
        sum sq negatives positives := by
  induction choices generalizing remaining sum sq negatives positives with
  | nil =>
      simp only [a15MagnitudeChoiceUsed, zero_add] at hcount
      simp only [a15MagnitudeChoiceSum, add_zero] at hsum
      simp only [a15MagnitudeChoiceSq, add_zero] at hsq
      subst remaining
      rw [hsum, hsq]
      have hcase : e7SmallNormCase targetSq = true := by
        simp only [e7SmallNormCase, decide_eq_true_eq]
        exact htargetSq
      simpa [e7SmallEnumerateByMagnitudeAux, hcase, hparity,
        a15MagnitudeChoiceNegatives, a15MagnitudeChoicePositives] using hparity
  | cons choice choices ih =>
      rcases choice with ⟨negativeCount, positiveCount⟩
      let m := choices.length + 1
      have hused :
          negativeCount + positiveCount +
              a15MagnitudeChoiceUsed choices + zeroCount = remaining := by
        simpa only [a15MagnitudeChoiceUsed, Nat.add_assoc] using hcount
      have hnegative : negativeCount < remaining + 1 := by omega
      have hpositive :
          positiveCount < remaining - negativeCount + 1 := by omega
      have htailCount :
          a15MagnitudeChoiceUsed choices + zeroCount =
            remaining - (negativeCount + positiveCount) := by omega
      have htailSum :
          (sum + ((positiveCount : ℤ) - negativeCount) * (m : ℤ)) +
              a15MagnitudeChoiceSum choices = 0 := by
        simpa only [a15MagnitudeChoiceSum, m, Nat.cast_add,
          Nat.cast_one, add_assoc] using hsum
      have htailSq :
          (sq + (negativeCount + positiveCount) * m ^ 2) +
              a15MagnitudeChoiceSq choices = targetSq := by
        simpa only [a15MagnitudeChoiceSq, m, add_assoc] using hsq
      have hfeasible :
          e7SmallMagnitudeFeasible m
            (remaining - (negativeCount + positiveCount))
            (sum + ((positiveCount : ℤ) - negativeCount) * (m : ℤ))
            (sq + (negativeCount + positiveCount) * m ^ 2) = true := by
        unfold e7SmallMagnitudeFeasible
        simp only [decide_eq_true_eq]
        have hsumBound := a15MagnitudeChoiceSum_natAbs_le choices
        have hmSub : m - 1 = choices.length := by simp [m]
        have hremainingEq :
            remaining - (negativeCount + positiveCount) =
              a15MagnitudeChoiceUsed choices + zeroCount :=
          htailCount.symm
        constructor
        · rcases htargetSq with rfl | rfl | rfl | rfl | rfl <;> omega
        · rw [hmSub]
          have hdiff :
              sum + ((positiveCount : ℤ) - negativeCount) * (m : ℤ) =
                -a15MagnitudeChoiceSum choices := by
            omega
          rw [hdiff, Int.natAbs_neg]
          have husedLe :
              a15MagnitudeChoiceUsed choices ≤
                remaining - (negativeCount + positiveCount) := by
            rw [hremainingEq]
            omega
          exact hsumBound.trans (Nat.mul_le_mul_right _ husedLe)
      have htailParity :
          e7SmallCommonParity
            ((negatives ++
                List.replicate negativeCount (-((m : ℕ) : ℤ))) ++
                a15MagnitudeChoiceNegatives choices ++
                List.replicate zeroCount 0 ++
                a15MagnitudeChoicePositives choices ++
                (List.replicate positiveCount ((m : ℕ) : ℤ) ++ positives)) =
              true := by
        simpa only [a15MagnitudeChoiceNegatives,
          a15MagnitudeChoicePositives, m, List.append_assoc] using hparity
      have hmemTail :=
        ih (remaining - (negativeCount + positiveCount))
          (sum + ((positiveCount : ℤ) - negativeCount) * (m : ℤ))
          (sq + (negativeCount + positiveCount) * m ^ 2)
          (negatives ++ List.replicate negativeCount (-((m : ℕ) : ℤ)))
          (List.replicate positiveCount ((m : ℕ) : ℤ) ++ positives)
          htailCount htailSum htailSq htailParity
      have hfeasible' :
          e7SmallMagnitudeFeasible (choices.length + 1)
            (remaining - (negativeCount + positiveCount))
            (sum + ((positiveCount : ℤ) - negativeCount) *
              ((choices.length : ℤ) + 1))
            (sq + (negativeCount + positiveCount) *
              (choices.length + 1) ^ 2) = true := by
        simpa only [m, Nat.cast_add, Nat.cast_one] using hfeasible
      simp only [List.length_cons, e7SmallEnumerateByMagnitudeAux,
        List.mem_flatMap, a15MagnitudeChoiceNegatives,
        a15MagnitudeChoicePositives]
      refine ⟨negativeCount, List.mem_range.mpr hnegative, ?_⟩
      refine ⟨positiveCount, List.mem_range.mpr hpositive, ?_⟩
      simp only [hfeasible', if_true]
      simpa only [m, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel_left, List.append_assoc] using hmemTail

/-- Canonical nondecreasing reconstruction at magnitudes at most six. -/
def e7SmallCanonicalCoordinates (coordinates : List ℤ) : List ℤ :=
  let choices := a15MagnitudeChoicesFrom coordinates 6
  a15MagnitudeChoiceNegatives choices ++
    List.replicate (coordinates.count 0) 0 ++
    a15MagnitudeChoicePositives choices

theorem e7SmallCanonicalCoordinates_perm
    (coordinates : List ℤ)
    (hbounds : ∀ z ∈ coordinates, -6 ≤ z ∧ z ≤ 6) :
    (e7SmallCanonicalCoordinates coordinates).Perm coordinates := by
  rw [List.perm_iff_count]
  intro z
  simp only [e7SmallCanonicalCoordinates, List.count_append,
    List.count_replicate,
    a15MagnitudeChoicesFrom_negative_count,
    a15MagnitudeChoicesFrom_positive_count]
  by_cases hzZero : z = 0
  · subst z
    simp
  by_cases hzNegative : z < 0
  · have hzUpper : z ≤ -1 := by omega
    have hzZero' : 0 ≠ z := Ne.symm hzZero
    have hzNotPositive : ¬(1 ≤ z ∧ z ≤ (6 : ℤ)) := by omega
    by_cases hzLower : -6 ≤ z
    · simp [hzZero', hzLower, hzUpper, hzNotPositive]
    · have hzCoordinates : z ∉ coordinates := by
        intro hmem
        have := (hbounds z hmem).1
        omega
      rw [List.count_eq_zero.mpr hzCoordinates]
      simp [hzZero', hzLower, hzUpper, hzNotPositive]
  · have hzLower : 1 ≤ z := by omega
    have hzZero' : 0 ≠ z := Ne.symm hzZero
    have hzNotNegative : ¬(-6 ≤ z ∧ z ≤ (-1 : ℤ)) := by omega
    by_cases hzUpper : z ≤ 6
    · simp [hzZero', hzLower, hzUpper, hzNotNegative]
    · have hzCoordinates : z ∉ coordinates := by
        intro hmem
        have := (hbounds z hmem).2
        omega
      rw [List.count_eq_zero.mpr hzCoordinates]
      simp [hzZero', hzLower, hzUpper, hzNotNegative]

theorem e7SmallCanonicalCoordinates_length (coordinates : List ℤ) :
    (e7SmallCanonicalCoordinates coordinates).length =
      a15MagnitudeChoiceUsed (a15MagnitudeChoicesFrom coordinates 6) +
        coordinates.count 0 := by
  unfold e7SmallCanonicalCoordinates
  rw [List.length_append, List.length_append, List.length_replicate]
  have h :=
    a15MagnitudeChoiceNegatives_length_add_positives
      (a15MagnitudeChoicesFrom coordinates 6)
  omega

theorem e7SmallCanonicalCoordinates_sum (coordinates : List ℤ) :
    (e7SmallCanonicalCoordinates coordinates).sum =
      a15MagnitudeChoiceSum (a15MagnitudeChoicesFrom coordinates 6) := by
  unfold e7SmallCanonicalCoordinates
  simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul,
    mul_zero, add_zero]
  simpa only [add_zero] using
    a15MagnitudeChoice_sum_reconstruction
      (a15MagnitudeChoicesFrom coordinates 6)

theorem e7SmallCanonicalCoordinates_sq_sum (coordinates : List ℤ) :
    ((e7SmallCanonicalCoordinates coordinates).map
        (fun z : ℤ => z * z)).sum =
      a15MagnitudeChoiceSq (a15MagnitudeChoicesFrom coordinates 6) := by
  unfold e7SmallCanonicalCoordinates
  simp only [List.map_append, List.sum_append, List.map_replicate,
    List.sum_replicate, nsmul_eq_mul, mul_zero, add_zero]
  simpa only [add_zero, List.map_append, List.sum_append] using
    a15MagnitudeChoice_sq_reconstruction
      (a15MagnitudeChoicesFrom coordinates 6)

/-- Structural completeness of the eight-coordinate recursion. -/
theorem e7SmallCanonicalCoordinates_mem_normProfiles
    (coordinates : List ℤ) (targetSq : ℕ)
    (htargetSq :
      targetSq = 8 ∨ targetSq = 16 ∨ targetSq = 24 ∨
        targetSq = 32 ∨ targetSq = 40)
    (hlength : coordinates.length = 8)
    (hbounds : ∀ z ∈ coordinates, -6 ≤ z ∧ z ≤ 6)
    (hsum : coordinates.sum = 0)
    (hsq : (coordinates.map (fun z : ℤ => z * z)).sum = targetSq)
    (hparity :
      e7SmallCommonParity (e7SmallCanonicalCoordinates coordinates) = true) :
    e7SmallCanonicalCoordinates coordinates ∈ e7SmallNormProfiles := by
  let choices := a15MagnitudeChoicesFrom coordinates 6
  have hchoicesLength : choices.length = 6 := by simp [choices]
  have hperm := e7SmallCanonicalCoordinates_perm coordinates hbounds
  have hcanonicalLength :
      (e7SmallCanonicalCoordinates coordinates).length = 8 :=
    hperm.length_eq.trans hlength
  have hcount :
      a15MagnitudeChoiceUsed choices + coordinates.count 0 = 8 := by
    rw [← e7SmallCanonicalCoordinates_length coordinates]
    exact hcanonicalLength
  have hchoiceSum : a15MagnitudeChoiceSum choices = 0 := by
    rw [← e7SmallCanonicalCoordinates_sum coordinates]
    exact hperm.sum_eq.trans hsum
  have hsqPerm :
      ((e7SmallCanonicalCoordinates coordinates).map
          (fun z : ℤ => z * z)).sum =
        (coordinates.map (fun z : ℤ => z * z)).sum :=
    (hperm.map (fun z : ℤ => z * z)).sum_eq
  have hchoiceSq : a15MagnitudeChoiceSq choices = targetSq := by
    have hchoiceSqInt :
        (a15MagnitudeChoiceSq choices : ℤ) = targetSq := by
      rw [← e7SmallCanonicalCoordinates_sq_sum coordinates, hsqPerm]
      exact hsq
    exact_mod_cast hchoiceSqInt
  have hmem :=
    e7SmallEnumerateByMagnitudeAux_contains_of_choices choices targetSq
      htargetSq 8 0 0 (coordinates.count 0) [] [] hcount
      (by simpa using hchoiceSum) (by simpa using hchoiceSq)
      (by simpa only [e7SmallCanonicalCoordinates, choices,
        List.nil_append, List.append_nil] using hparity)
  rw [hchoicesLength] at hmem
  simpa only [e7SmallNormProfiles, e7SmallCanonicalCoordinates, choices,
    List.nil_append, List.append_nil] using hmem

/-- The signed-magnitude computation evaluates to exactly 25 profiles. -/
theorem e7SmallNormProfiles_eq_mined :
    e7SmallNormProfiles.toFinset = e7MinedComponentProfiles.toFinset := by
  change e7MinedNormProfiles.toFinset = e7MinedNormProfileData.toFinset
  rw [e7MinedNormProfiles]
  rw [e7MinedEnumerateByMagnitudeAux_eq_frontier 4 2]
  rw [e7MinedFrontier2_checked, e7MinedNormSearchOutput_checked,
    e7MinedNormSearchOutput_toFinset]

/-- Completeness stated against the explicit 25-profile normal form. -/
theorem e7SmallCanonicalCoordinates_mem_minedProfiles
    (coordinates : List ℤ) (targetSq : ℕ)
    (htargetSq :
      targetSq = 8 ∨ targetSq = 16 ∨ targetSq = 24 ∨
        targetSq = 32 ∨ targetSq = 40)
    (hlength : coordinates.length = 8)
    (hbounds : ∀ z ∈ coordinates, -6 ≤ z ∧ z ≤ 6)
    (hsum : coordinates.sum = 0)
    (hsq : (coordinates.map (fun z : ℤ => z * z)).sum = targetSq)
    (hparity :
      e7SmallCommonParity (e7SmallCanonicalCoordinates coordinates) = true) :
    e7SmallCanonicalCoordinates coordinates ∈ e7MinedComponentProfiles := by
  have hmem := e7SmallCanonicalCoordinates_mem_normProfiles coordinates
    targetSq htargetSq hlength hbounds hsum hsq hparity
  have hfin :
      e7SmallCanonicalCoordinates coordinates ∈ e7SmallNormProfiles.toFinset :=
    List.mem_toFinset.mpr hmem
  rw [e7SmallNormProfiles_eq_mined] at hfin
  exact List.mem_toFinset.mp hfin

/-- The invariant package mined in the lattice branch factors through one of
the 25 explicit divided profiles, up to a coordinate permutation. -/
theorem e7Profile_factors_through_mined
    (profile : Fin 8 → ℤ)
    (hfive : ∀ i, (5 : ℤ) ∣ profile i)
    (hsum : ∑ i, profile i = 0)
    (n : ℤ)
    (hn : n = 50 ∨ n = 100 ∨ n = 150 ∨ n = 200 ∨ n = 250)
    (hsq : ∑ i, (profile i) ^ 2 = 4 * n)
    (hparity : ∀ i j, profile i % 2 = profile j % 2) :
    ∃ coordinates ∈ e7MinedComponentProfiles,
      (coordinates.map fun z => 5 * z).Perm (List.ofFn profile) := by
  classical
  choose z hz using hfive
  obtain ⟨targetSq, htargetSq, htargetEq⟩ :
      ∃ targetSq : ℕ,
        (targetSq = 8 ∨ targetSq = 16 ∨ targetSq = 24 ∨
          targetSq = 32 ∨ targetSq = 40) ∧
        4 * n = 25 * (targetSq : ℤ) := by
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact ⟨8, Or.inl rfl, by norm_num⟩
    · exact ⟨16, Or.inr (Or.inl rfl), by norm_num⟩
    · exact ⟨24, Or.inr (Or.inr (Or.inl rfl)), by norm_num⟩
    · exact ⟨32, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by norm_num⟩
    · exact ⟨40, Or.inr (Or.inr (Or.inr (Or.inr rfl))), by norm_num⟩
  have hzsum : ∑ i, z i = 0 := by
    have hscaled : 5 * ∑ i, z i = 0 := by
      calc
        5 * ∑ i, z i = ∑ i, 5 * z i := by rw [Finset.mul_sum]
        _ = ∑ i, profile i :=
          Finset.sum_congr rfl fun i _ => (hz i).symm
        _ = 0 := hsum
    omega
  have hzsq : ∑ i, (z i) ^ 2 = (targetSq : ℤ) := by
    have hscaled : 25 * ∑ i, (z i) ^ 2 = 4 * n := by
      calc
        25 * ∑ i, (z i) ^ 2 = ∑ i, (5 * z i) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ i, (profile i) ^ 2 :=
          Finset.sum_congr rfl fun i _ => by rw [hz i]
        _ = 4 * n := hsq
    rw [htargetEq] at hscaled
    omega
  have htargetLe : targetSq ≤ 40 := by
    rcases htargetSq with rfl | rfl | rfl | rfl | rfl <;> omega
  have hzbound : ∀ i, -6 ≤ z i ∧ z i ≤ 6 := by
    intro i
    have hle : z i ^ 2 ≤ ∑ j, (z j) ^ 2 :=
      Finset.single_le_sum (f := fun j => (z j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hzsq] at hle
    constructor <;> nlinarith
  let raw := List.ofFn z
  let canonical := e7SmallCanonicalCoordinates raw
  have hrawBounds : ∀ q ∈ raw, -6 ≤ q ∧ q ≤ 6 :=
    List.forall_mem_ofFn_iff.mpr hzbound
  have hperm : canonical.Perm raw :=
    e7SmallCanonicalCoordinates_perm raw hrawBounds
  have hrawParity : ∀ q ∈ raw, q % 2 = z 0 % 2 := by
    change ∀ q ∈ List.ofFn z, q % 2 = z 0 % 2
    rw [List.forall_mem_ofFn_iff]
    intro i
    have h := hparity i 0
    rw [hz i, hz 0] at h
    omega
  have hcanonicalParity :
      ∀ q ∈ canonical, q % 2 = z 0 % 2 := by
    intro q hq
    exact hrawParity q (hperm.mem_iff.mp hq)
  have hcanonicalLength : canonical.length = 8 :=
    hperm.length_eq.trans (by simp [raw])
  have hzeroMem : canonical.getD 0 0 ∈ canonical := by
    rw [List.getD_eq_getElem _ 0 (by omega)]
    exact List.getElem_mem (by omega)
  have hcommon : e7SmallCommonParity canonical = true :=
    e7SmallCommonParity_of_mod_eq canonical (z 0 % 2)
      hcanonicalParity (hcanonicalParity _ hzeroMem)
  have hrawSum : raw.sum = 0 := by
    change (List.ofFn z).sum = 0
    rw [List.sum_ofFn]
    exact hzsum
  have hrawSq :
      (raw.map (fun q : ℤ => q * q)).sum = targetSq := by
    change ((List.ofFn z).map (fun q : ℤ => q * q)).sum = targetSq
    rw [List.map_ofFn, List.sum_ofFn]
    calc
      ∑ i, (Function.comp (fun q : ℤ => q * q) z) i =
          ∑ i, (z i) ^ 2 :=
        Finset.sum_congr rfl fun i _ => by
          simp [Function.comp_apply, pow_two]
      _ = targetSq := hzsq
  have hmem : canonical ∈ e7MinedComponentProfiles := by
    exact e7SmallCanonicalCoordinates_mem_minedProfiles raw targetSq
      htargetSq (by simp [raw]) hrawBounds hrawSum hrawSq
      (by simpa only [canonical] using hcommon)
  refine ⟨canonical, hmem, ?_⟩
  have hmapPerm := hperm.map (fun q : ℤ => 5 * q)
  have hyList : (raw.map fun q : ℤ => 5 * q) = List.ofFn profile := by
    change (List.ofFn z).map (fun q : ℤ => 5 * q) = List.ofFn profile
    rw [List.map_ofFn]
    rw [List.ofFn_inj]
    funext i
    simp only [Function.comp_apply]
    exact (hz i).symm
  simpa only [hyList] using hmapPerm

theorem e7MinedComponentProfiles_length :
    e7MinedComponentProfiles.length = 25 := by
  rfl

/-- Every explicit mined profile is in the canonical nondecreasing order. -/
theorem e7MinedComponentProfiles_pairwise
    (coordinates : List ℤ)
    (hcoordinates : coordinates ∈ e7MinedComponentProfiles) :
    coordinates.Pairwise (· ≤ ·) := by
  have hall :
      e7MinedComponentProfiles.all
        (fun profile => decide (profile.Pairwise (· ≤ ·))) = true := by
    decide +kernel
  exact of_decide_eq_true
    ((List.all_eq_true.mp hall) coordinates hcoordinates)

/-- Scale a divided component back to the half-block convention. -/
def e7SmallProfile (coordinates : List ℤ) : Fin 8 → ℤ :=
  fun i => 5 * coordinates.getD i.1 0

end SRG266
