/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15ExactEnumeration
import SRG266.Hosts.A15ReducedProfile
import Mathlib.Data.List.GetD

/-!
# Soundness of the direct A15 reference count

The optimized reference enumerator sums four reduced coordinates directly
from the checked 1,820-subset array.  This module proves that its count is
the cardinality of the declarative `A15EligibleIndex` finite type.
-/

namespace SRG266

set_option maxRecDepth 100000

theorem a15DataSubsetSum_scale_reduced
    (residue : ℤ) (coordinates : List ℤ)
    (hlength : coordinates.length = 16)
    (s : A15FourSubsetIndex) :
    a15DataSubsetSum
        (a15EnumerationProfile
          (a15ScaleReducedProfile residue coordinates))
        (a15FourSubsetAt s) =
      4 * a15ReducedDataSubsetSum coordinates
          (a15FourSubsetAt s) +
        4 * residue := by
  have hinc := a15FourSubsetAt_increasing s
  rcases hinc with ⟨hab, hbc, hcd, hd⟩
  have ha : (a15FourSubsetAt s).a < 16 := by omega
  have hb : (a15FourSubsetAt s).b < 16 := by omega
  have hc : (a15FourSubsetAt s).c < 16 := by omega
  unfold a15DataSubsetSum A15FourSubset.valueSum
    A15FourSubset.coordinates a15ReducedDataSubsetSum
    a15FourSubsetCoordinate
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  simp only [a15EnumerationProfile_scale_apply residue coordinates hlength]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd]
  ring

theorem a15ReducedDataEligible_iff
    (residue : ℤ) (coordinates : List ℤ)
    (hlength : coordinates.length = 16)
    (s : A15FourSubsetIndex) :
    a15ReducedDataEligible residue coordinates
        (a15FourSubsetAt s) = true ↔
      a15Eligible
        (a15EnumerationProfile
          (a15ScaleReducedProfile residue coordinates)) s := by
  rw [a15ReducedDataEligible, Bool.or_eq_true]
  simp only [decide_eq_true_eq]
  unfold a15Eligible a15DataEligible
  rw [a15DataSubsetSum_scale_reduced residue coordinates hlength s]
  constructor
  · intro h
    rcases h with h | h
    · right
      omega
    · left
      omega
  · intro h
    rcases h with h | h
    · right
      omega
    · left
      omega

private theorem a15Nat_sum_get
    {α : Type*} (l : List α) (f : α → ℕ) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  rw [List.ofFn_comp', List.ofFn_get]

private theorem a15Nat_foldl_add
    {α : Type*} (l : List α) (f : α → ℕ) (initial : ℕ) :
    l.foldl (fun total x => total + f x) initial =
      initial + (l.map f).sum := by
  induction l generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      omega

theorem a15ExactEligibleCardReduced_eq_sum
    (residue : ℤ) (coordinates : List ℤ) :
    a15ExactEligibleCardReduced residue coordinates =
      ∑ s : A15FourSubsetIndex,
        if a15ReducedDataEligible residue coordinates
            (a15FourSubsetAt s) then 1 else 0 := by
  unfold a15ExactEligibleCardReduced
  rw [← Array.foldl_toList, a15Nat_foldl_add]
  simp only [zero_add]
  rw [← a15Nat_sum_get]
  rfl

theorem a15EligibleIndex_card_eq_sum
    (d : Fin 16 → ℤ) :
    Fintype.card (A15EligibleIndex d) =
      ∑ s : A15FourSubsetIndex,
        if a15Eligible d s then 1 else 0 := by
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]

/-- The optimized direct reference count is exactly the cardinality of the
declarative eligible shell. -/
theorem a15ExactEligibleCardReduced_eq_card
    (residue : ℤ) (coordinates : List ℤ)
    (hlength : coordinates.length = 16) :
    a15ExactEligibleCardReduced residue coordinates =
      Fintype.card
        (A15EligibleIndex
          (a15EnumerationProfile
            (a15ScaleReducedProfile residue coordinates))) := by
  rw [a15ExactEligibleCardReduced_eq_sum,
    a15EligibleIndex_card_eq_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hiff :=
    a15ReducedDataEligible_iff residue coordinates hlength s
  cases hbool :
      a15ReducedDataEligible residue coordinates (a15FourSubsetAt s)
  · have hnot :
        ¬a15Eligible
          (a15EnumerationProfile
            (a15ScaleReducedProfile residue coordinates)) s := by
        intro heligible
        have := hiff.mpr heligible
        simp [hbool] at this
    simp [hnot]
  · have heligible :
        a15Eligible
          (a15EnumerationProfile
            (a15ScaleReducedProfile residue coordinates)) s :=
        hiff.mp (by simp [hbool])
    simp [heligible]

end SRG266
