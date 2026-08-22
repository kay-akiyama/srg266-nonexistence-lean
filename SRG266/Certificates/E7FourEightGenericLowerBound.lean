/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7FourEightGenericSupportKernel
import SRG266.Certificates.E7FourEightGenericAggregateKernel

/-!
# Kernel-only lower bound for the generic E7 class-2 profile

The structural proof exhausts the 32,768 masks of one T(6) layer in bounded
blocks, retains 163 candidates,
and checks their 163 squared matched-layer pairs.  Ordinary counting then
handles every surviving support type and proves that a nonzero exact profile
has total at least 60.
-/

open scoped BigOperators

namespace SRG266
namespace E7FourEightGenericData

theorem class2_layer_zero_of_mask_eq_zero
    (m : Class2Index → ProfileValue) (side : Bool)
    (hmask : class2LayerSupportMask m side = 0#15) (e : Fin 15) :
    (m (class2LayerIndex side e)).1 = 0 := by
  have hbit := class2LayerSupportMask_getElem m side e
  rw [hmask] at hbit
  simp only [BitVec.getElem_zero] at hbit
  by_contra hne
  simp [hne] at hbit

theorem class2_layer_nonzero_of_mask_bit
    (m : Class2Index → ProfileValue) (side : Bool) (e : Fin 15)
    (hbit : (class2LayerSupportMask m side)[e.1] = true) :
    (m (class2LayerIndex side e)).1 ≠ 0 := by
  simpa only [class2LayerSupportMask_getElem, decide_eq_true_eq] using hbit

theorem class2_fourteen_arithmetic_impossible (x y : Nat)
    (hxy₁ : 7 * x + 4 * y = 240)
    (hxy₂ : 3 * x + 7 * y = 180) : False := by
  omega

theorem class2MissingAdjacent_rows_eq
    (w : Fin 15 → Nat) (e : Fin 15)
    (heq : ∀ f : Fin 15, f ≠ e →
      class2LayerNeighbourSum w f + 3 * w f = 30) :
    (∑ f ∈ class2MissingAdjacent e,
        (class2LayerNeighbourSum w f + 3 * w f)) = 240 := by
  calc
    (∑ f ∈ class2MissingAdjacent e,
        (class2LayerNeighbourSum w f + 3 * w f)) =
        ∑ _f ∈ class2MissingAdjacent e, 30 := by
      apply Finset.sum_congr rfl
      intro f hf
      exact heq f (class2MissingAdjacent_ne e f hf)
    _ = 240 := by
      rw [Finset.sum_const, nsmul_eq_mul, class2MissingAdjacent_card]
      norm_num

theorem class2MissingNonadjacent_rows_eq
    (w : Fin 15 → Nat) (e : Fin 15)
    (heq : ∀ f : Fin 15, f ≠ e →
      class2LayerNeighbourSum w f + 3 * w f = 30) :
    (∑ f ∈ class2MissingNonadjacent e,
        (class2LayerNeighbourSum w f + 3 * w f)) = 180 := by
  calc
    (∑ f ∈ class2MissingNonadjacent e,
        (class2LayerNeighbourSum w f + 3 * w f)) =
        ∑ _f ∈ class2MissingNonadjacent e, 30 := by
      apply Finset.sum_congr rfl
      intro f hf
      exact heq f (class2MissingNonadjacent_ne e f hf)
    _ = 180 := by
      rw [Finset.sum_const, nsmul_eq_mul,
        class2MissingNonadjacent_card]
      norm_num

theorem class2_one_layer_fourteen_impossible
    (m : Class2Index → ProfileValue)
    (h : ProfileSatisfies class2Adjacent m) (side : Bool)
    (hotherMask : class2LayerSupportMask m (!side) = 0#15)
    (hcard : class2MaskCard (class2LayerSupportMask m side) = 14) :
    False := by
  let w : Fin 15 → Nat :=
    fun f => (m (class2LayerIndex side f)).1
  have hother (f : Fin 15) :
      (m (class2LayerIndex (!side) f)).1 = 0 :=
    class2_layer_zero_of_mask_eq_zero m (!side) hotherMask f
  rcases class2Mask_card_fourteen_has_single_missing
      (class2LayerSupportMask m side) hcard with ⟨e, hezero, hefull⟩
  have hwzero : w e = 0 := by
    unfold w
    by_contra hne
    have htrue : (class2LayerSupportMask m side)[e.1] = true := by
      simpa only [class2LayerSupportMask_getElem, decide_eq_true_eq]
        using hne
    rw [hezero] at htrue
    contradiction
  have heq (f : Fin 15) (hf : f ≠ e) :
      class2LayerNeighbourSum w f + 3 * w f = 30 := by
    have hbit := hefull f hf
    have hnonzero := class2_layer_nonzero_of_mask_bit m side f hbit
    have hrow := h (class2LayerIndex side f) hnonzero
    rw [class2_profileNeighbourSum_layer m side f hother] at hrow
    exact hrow
  let x := ∑ f ∈ class2MissingAdjacent e, w f
  let y := ∑ f ∈ class2MissingNonadjacent e, w f
  have hxrows := class2MissingAdjacent_rows_eq w e heq
  have hyrows := class2MissingNonadjacent_rows_eq w e heq
  have hxidentity := class2MissingAdjacent_aggregate w e hwzero
  have hyidentity := class2MissingNonadjacent_aggregate w e
  have hxy₁ : 7 * x + 4 * y = 240 := by
    dsimp [x, y]
    exact hxidentity.symm.trans hxrows
  have hxy₂ : 3 * x + 7 * y = 180 := by
    dsimp [x, y]
    exact hyidentity.symm.trans hyrows
  exact class2_fourteen_arithmetic_impossible x y hxy₁ hxy₂

theorem class2_one_layer_fifteen_impossible
    (m : Class2Index → ProfileValue)
    (h : ProfileSatisfies class2Adjacent m) (side : Bool)
    (hotherMask : class2LayerSupportMask m (!side) = 0#15)
    (hcard : class2MaskCard (class2LayerSupportMask m side) = 15) :
    False := by
  let w : Fin 15 → Nat :=
    fun f => (m (class2LayerIndex side f)).1
  have hother (f : Fin 15) :
      (m (class2LayerIndex (!side) f)).1 = 0 :=
    class2_layer_zero_of_mask_eq_zero m (!side) hotherMask f
  have hfull := class2Mask_card_fifteen_is_full
    (class2LayerSupportMask m side) hcard
  have heq (f : Fin 15) :
      class2LayerNeighbourSum w f + 3 * w f = 30 := by
    have hnonzero := class2_layer_nonzero_of_mask_bit m side f (hfull f)
    have hrow := h (class2LayerIndex side f) hnonzero
    rw [class2_profileNeighbourSum_layer m side f hother] at hrow
    exact hrow
  have hrows :
      (∑ f : Fin 15, (class2LayerNeighbourSum w f + 3 * w f)) = 450 := by
    calc
      (∑ f : Fin 15, (class2LayerNeighbourSum w f + 3 * w f)) =
          ∑ _f : Fin 15, 30 := by
        apply Finset.sum_congr rfl
        intro f hf
        exact heq f
      _ = 450 := by norm_num
  have haggregate := class2Full_aggregate w
  omega

theorem class2_profileTotal_eq_zero_of_masks
    (m : Class2Index → ProfileValue)
    (hleft : class2LayerSupportMask m false = 0#15)
    (hright : class2LayerSupportMask m true = 0#15) :
    profileTotal m = 0 := by
  have hcard := class2_profileSupport_card m
  have hzero : class2MaskCard 0#15 = 0 := by decide +kernel
  simp only [hleft, hright, hzero] at hcard
  have hempty : profileSupport m = ∅ := Finset.card_eq_zero.mp (by omega)
  have hsum := sum_profileSupport m
  rw [hempty] at hsum
  simpa using hsum.symm

theorem class2_support_degree_seven_of_equal_masks
    (m : Class2Index → ProfileValue)
    (hequal : class2LayerSupportMask m false =
      class2LayerSupportMask m true)
    (hdegree : ∀ e : Fin 15,
      (class2LayerSupportMask m false)[e.1] = true →
        class2MaskInnerDegree (class2LayerSupportMask m false) e = 6) :
    ∀ j ∈ profileSupport m,
      supportInDegree class2Adjacent (profileSupport m) j = 7 := by
  intro j hj
  rcases class2LayerIndex_bijective.2 j with ⟨⟨side, e⟩, rfl⟩
  have hnonzero := (mem_profileSupport m (class2LayerIndex side e)).1 hj
  have hbit : (class2LayerSupportMask m side)[e.1] = true := by
    simpa only [class2LayerSupportMask_getElem, decide_eq_true_eq]
      using hnonzero
  rw [class2_supportInDegree_layer]
  fin_cases side
  · simp only [Bool.not_true] at hbit ⊢
    have hleftbit : (class2LayerSupportMask m false)[e.1] = true := by
      rw [hequal]
      exact hbit
    rw [← hequal, hdegree e hleftbit]
    simp [hleftbit]
  · simp only [Bool.not_false] at hbit ⊢
    have hrightbit : (class2LayerSupportMask m true)[e.1] = true := by
      rw [← hequal]
      exact hbit
    rw [hdegree e hbit]
    simp [hrightbit]

theorem class2ProfileTotalLowerBound
    (m : Class2Index → ProfileValue)
    (h : ProfileSatisfies class2Adjacent m) :
    profileTotal m = 0 ∨ 60 ≤ profileTotal m := by
  let left := class2LayerSupportMask m false
  let right := class2LayerSupportMask m true
  have hclassification : class2PairConclusion left right :=
    class2PairConclusion_of_admissible left right
      (class2_pairAdmissible_of_satisfies m h)
  rcases hclassification with hzero | honeRight | honeLeft | hboth
  · left
    exact class2_profileTotal_eq_zero_of_masks m hzero.1 hzero.2
  · rcases honeRight.2 with hfourteen | hfifteen
    · exact False.elim (class2_one_layer_fourteen_impossible m h true
        (by simpa [left, right] using honeRight.1) (by simpa [right] using hfourteen))
    · exact False.elim (class2_one_layer_fifteen_impossible m h true
        (by simpa [left, right] using honeRight.1) (by simpa [right] using hfifteen))
  · rcases honeLeft.2 with hfourteen | hfifteen
    · exact False.elim (class2_one_layer_fourteen_impossible m h false
        (by simpa [left, right] using honeLeft.1) (by simpa [left] using hfourteen))
    · exact False.elim (class2_one_layer_fifteen_impossible m h false
        (by simpa [left, right] using honeLeft.1) (by simpa [left] using hfifteen))
  · right
    rcases hboth.2.2 with hlarge | hspecial
    · apply profileTotal_ge_sixty_of_support_card class2Adjacent m h
        (fun j hj => class2_supportInDegree_le_nine (profileSupport m) j)
      rw [class2_profileSupport_card]
      simpa [left, right] using hlarge
    · have hsupportCard : (profileSupport m).card = 20 := by
        rw [class2_profileSupport_card]
        have hrightCard : class2MaskCard right = 10 := by
          rw [← hspecial.1]
          exact hspecial.2.1
        simp [left, right, hspecial.2.1, hrightCard]
      have hequal : class2LayerSupportMask m false =
          class2LayerSupportMask m true := by
        simpa [left, right] using hspecial.1
      have hdegree : ∀ e : Fin 15,
          (class2LayerSupportMask m false)[e.1] = true →
            class2MaskInnerDegree (class2LayerSupportMask m false) e = 6 := by
        simpa [left] using hspecial.2.2
      rw [profileTotal_eq_sixty_of_support_degree_seven
        class2Adjacent m h
        (class2_support_degree_seven_of_equal_masks m hequal hdegree)
        hsupportCard]

end E7FourEightGenericData
end SRG266
