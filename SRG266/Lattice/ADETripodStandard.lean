/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.ADETripodCoordinates

/-!
# Standard ADE coordinates for tripods

This file identifies the surviving tripod shapes with the existing `D` and
`E` Gram matrices.  The `D` coordinate change is uniform in the long-arm
length; the three exceptional coordinate changes are closed finite maps.
-/

namespace SRG266
namespace Lattice

open SimpleGraph

/-! ## The `D` family -/

/-- Standard `D_(t+3)` coordinates mapped to arms `(1,1,t)`. -/
def dTripodMap (t : ℕ) (i : Fin (t + 3)) : TripodVertex 1 1 t :=
  if hlong : i.1 < t then
    some (.inr (.inr ⟨t - 1 - i.1, by omega⟩))
  else if hcenter : i.1 = t then none
  else if hshort₀ : i.1 = t + 1 then some (.inl 0)
  else some (.inr (.inl 0))

/-- Inverse to `dTripodMap`. -/
def dTripodInv (t : ℕ) (_ht : 0 < t) : TripodVertex 1 1 t → Fin (t + 3)
  | none => ⟨t, by omega⟩
  | some (.inl _) => ⟨t + 1, by omega⟩
  | some (.inr (.inl _)) => ⟨t + 2, by omega⟩
  | some (.inr (.inr j)) => ⟨t - 1 - j.1, by omega⟩

/-- The uniform vertex equivalence between `D_(t+3)` and its tripod. -/
def dTripodEquiv (t : ℕ) (ht : 0 < t) : Fin (t + 3) ≃ TripodVertex 1 1 t where
  toFun := dTripodMap t
  invFun := dTripodInv t ht
  left_inv := by
    intro i
    simp only [dTripodMap]
    split_ifs with hlong hcenter hshort₀
    · apply Fin.ext
      simp only [dTripodInv]
      omega
    · apply Fin.ext
      simp only [dTripodInv]
      omega
    · apply Fin.ext
      simp only [dTripodInv]
      omega
    · apply Fin.ext
      simp only [dTripodInv]
      omega
  right_inv := by
    intro x
    rcases x with _ | x
    · simp [dTripodInv, dTripodMap]
    · rcases x with i | x
      · fin_cases i
        simp [dTripodInv, dTripodMap]
      · rcases x with i | j
        · fin_cases i
          simp [dTripodInv, dTripodMap]
        · simp only [dTripodInv]
          have hlt : t - 1 - j.1 < t := by omega
          rw [dTripodMap, dif_pos hlt]
          apply congr_arg (fun k : Fin t ↦
            (some (Sum.inr (Sum.inr k)) : TripodVertex 1 1 t))
          apply Fin.ext
          change t - 1 - (t - 1 - j.1) = j.1
          omega

theorem revNat_eq_iff {t i j : ℕ} (hi : i < t) (hj : j < t) :
    t - 1 - i = t - 1 - j ↔ i = j := by omega

theorem revNat_eq_zero_iff {t i : ℕ} (hi : i < t) :
    t - 1 - i = 0 ↔ i + 1 = t := by omega

theorem revNat_adj_iff {t i j : ℕ} (hi : i < t) (hj : j < t) :
    (t - 1 - i) + 1 = t - 1 - j ∨ (t - 1 - j) + 1 = t - 1 - i ↔
      i + 1 = j ∨ j + 1 = i := by omega

/-- In the uniform coordinates, the `(1,1,t)` tripod Cartan matrix is
`D_(t+3)`. -/
theorem graphCartanMatrix_dTripod (t : ℕ) (ht : 0 < t) (i j : Fin (t + 3)) :
    graphCartanMatrix (tripodGraph 1 1 t) (dTripodEquiv t ht i)
      (dTripodEquiv t ht j) = gramD (t + 3) i j := by
  classical
  simp only [dTripodEquiv]
  simp [graphCartanMatrix, tripodGraph, SimpleGraph.fromRel_adj,
    tripodRel, tripodArmRel, tripodArmZero, dTripodMap, gramD, gramDEntry,
    SimpleGraph.pathGraph_adj]
  split_ifs <;> simp_all [revNat_eq_iff, revNat_eq_zero_iff, revNat_adj_iff] <;> omega

/-! ## The exceptional diagrams -/

def e6TripodMap : Fin 6 → TripodVertex 1 2 2 := ![
  some (.inr (.inl 1)), some (.inr (.inl 0)), none,
  some (.inr (.inr 0)), some (.inr (.inr 1)), some (.inl 0)]

def e7TripodMap : Fin 7 → TripodVertex 1 2 3 := ![
  some (.inr (.inl 1)), some (.inr (.inl 0)), none,
  some (.inr (.inr 0)), some (.inr (.inr 1)), some (.inr (.inr 2)),
  some (.inl 0)]

def e8TripodMap : Fin 8 → TripodVertex 1 2 4 := ![
  some (.inr (.inl 1)), some (.inr (.inl 0)), none,
  some (.inr (.inr 0)), some (.inr (.inr 1)), some (.inr (.inr 2)),
  some (.inr (.inr 3)), some (.inl 0)]

noncomputable def e6TripodEquiv : Fin 6 ≃ TripodVertex 1 2 2 :=
  Equiv.ofBijective e6TripodMap (by decide)

noncomputable def e7TripodEquiv : Fin 7 ≃ TripodVertex 1 2 3 :=
  Equiv.ofBijective e7TripodMap (by decide)

noncomputable def e8TripodEquiv : Fin 8 ≃ TripodVertex 1 2 4 :=
  Equiv.ofBijective e8TripodMap (by decide)

theorem graphCartanMatrix_e6Tripod (i j : Fin 6) :
    graphCartanMatrix (tripodGraph 1 2 2) (e6TripodEquiv i)
      (e6TripodEquiv j) = gramE 6 i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [graphCartanMatrix, tripodGraph, SimpleGraph.fromRel_adj,
      tripodRel, tripodArmRel, tripodArmZero, e6TripodEquiv, e6TripodMap,
      gramE, gramEEntry, SimpleGraph.pathGraph_adj] <;> decide

theorem graphCartanMatrix_e7Tripod (i j : Fin 7) :
    graphCartanMatrix (tripodGraph 1 2 3) (e7TripodEquiv i)
      (e7TripodEquiv j) = gramE 7 i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [graphCartanMatrix, tripodGraph, SimpleGraph.fromRel_adj,
      tripodRel, tripodArmRel, tripodArmZero, e7TripodEquiv, e7TripodMap,
      gramE, gramEEntry, SimpleGraph.pathGraph_adj] <;> decide

theorem graphCartanMatrix_e8Tripod (i j : Fin 8) :
    graphCartanMatrix (tripodGraph 1 2 4) (e8TripodEquiv i)
      (e8TripodEquiv j) = gramE 8 i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [graphCartanMatrix, tripodGraph, SimpleGraph.fromRel_adj,
      tripodRel, tripodArmRel, tripodArmZero, e8TripodEquiv, e8TripodMap,
      gramE, gramEEntry, SimpleGraph.pathGraph_adj] <;> decide

end Lattice
end SRG266
