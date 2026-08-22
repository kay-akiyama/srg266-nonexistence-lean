/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7FourEightGenericSupport

/-!
# One-layer arithmetic for the generic E7 class-2 graph

The class-2 graph is two matched copies of the triangular graph T(6).  These
explicit neighbour tables support the ordinary algebraic proof that a profile
cannot occupy exactly fourteen or fifteen vertices of only one layer.
-/

open scoped BigOperators

namespace SRG266
namespace E7FourEightGenericData


def class2MissingAdjacent (e : Fin 15) : Finset (Fin 15) :=
  ![{1, 2, 3, 4, 5, 6, 7, 8},
    {0, 2, 3, 4, 5, 9, 10, 11},
    {0, 1, 3, 4, 6, 9, 12, 13},
    {0, 1, 2, 4, 7, 10, 12, 14},
    {0, 1, 2, 3, 8, 11, 13, 14},
    {0, 1, 6, 7, 8, 9, 10, 11},
    {0, 2, 5, 7, 8, 9, 12, 13},
    {0, 3, 5, 6, 8, 10, 12, 14},
    {0, 4, 5, 6, 7, 11, 13, 14},
    {1, 2, 5, 6, 10, 11, 12, 13},
    {1, 3, 5, 7, 9, 11, 12, 14},
    {1, 4, 5, 8, 9, 10, 13, 14},
    {2, 3, 6, 7, 9, 10, 13, 14},
    {2, 4, 6, 8, 9, 11, 12, 14},
    {3, 4, 7, 8, 10, 11, 12, 13}] e

def class2MissingNonadjacent (e : Fin 15) : Finset (Fin 15) :=
  ![{9, 10, 11, 12, 13, 14}, {6, 7, 8, 12, 13, 14},
    {5, 7, 8, 10, 11, 14}, {5, 6, 8, 9, 11, 13},
    {5, 6, 7, 9, 10, 12}, {2, 3, 4, 12, 13, 14},
    {1, 3, 4, 10, 11, 14}, {1, 2, 4, 9, 11, 13},
    {1, 2, 3, 9, 10, 12}, {0, 3, 4, 7, 8, 14},
    {0, 2, 4, 6, 8, 13}, {0, 2, 3, 6, 7, 12},
    {0, 1, 4, 5, 8, 11}, {0, 1, 3, 5, 7, 10},
    {0, 1, 2, 5, 6, 9}] e

def class2LayerNeighbourSum (w : Fin 15 → Nat) (e : Fin 15) : Nat :=
  ∑ f ∈ class2MissingAdjacent e, w f

theorem class2MissingAdjacent_card (e : Fin 15) :
    (class2MissingAdjacent e).card = 8 := by
  fin_cases e <;> decide +kernel

theorem class2MissingNonadjacent_card (e : Fin 15) :
    (class2MissingNonadjacent e).card = 6 := by
  fin_cases e <;> decide +kernel

theorem class2MissingAdjacent_ne (e f : Fin 15)
    (h : f ∈ class2MissingAdjacent e) : f ≠ e := by
  decide +kernel +revert

theorem class2MissingNonadjacent_ne (e f : Fin 15)
    (h : f ∈ class2MissingNonadjacent e) : f ≠ e := by
  decide +kernel +revert

theorem class2MissingAdjacent_mem (e f : Fin 15) :
    f ∈ class2MissingAdjacent e ↔
      class2Adjacent (class2LayerIndex false e)
        (class2LayerIndex false f) = true := by
  decide +kernel +revert

theorem class2LayerNeighbourSum_eq_full
    (w : Fin 15 → Nat) (e : Fin 15) :
    class2LayerNeighbourSum w e =
      ∑ f : Fin 15,
        if class2Adjacent (class2LayerIndex false e)
            (class2LayerIndex false f) = true then w f else 0 := by
  unfold class2LayerNeighbourSum
  rw [← Finset.sum_filter]
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact class2MissingAdjacent_mem e f

theorem class2_profileNeighbourSum_layer
    (m : Class2Index → ProfileValue) (side : Bool) (e : Fin 15)
    (hother : ∀ f : Fin 15,
      (m (class2LayerIndex (!side) f)).1 = 0) :
    profileNeighbourSum class2Adjacent m (class2LayerIndex side e) =
      class2LayerNeighbourSum
        (fun f => (m (class2LayerIndex side f)).1) e := by
  unfold profileNeighbourSum profileNeighbours
  rw [Finset.sum_filter]
  calc
    (∑ j : Class2Index,
        if class2Adjacent (class2LayerIndex side e) j = true
          then (m j).1 else 0) =
      ∑ p : Bool × Fin 15,
        if class2Adjacent (class2LayerIndex side e)
            (class2LayerEquiv p) = true
          then (m (class2LayerEquiv p)).1 else 0 := by
      symm
      apply Fintype.sum_equiv class2LayerEquiv
      intro p
      rfl
    _ = class2LayerNeighbourSum
        (fun f => (m (class2LayerIndex side f)).1) e := by
      fin_cases side <;>
        simp only [Fintype.sum_prod_type, class2LayerEquiv_apply]
      · rw [sum_bool_nat]
        have hz (f : Fin 15) :
            (m (class2LayerIndex false f)).1 = 0 := by
          simpa using hother f
        simp_rw [hz]
        rw [class2LayerNeighbourSum_eq_full]
        simp [class2Adjacent_true_true]
      · rw [sum_bool_nat]
        have hz (f : Fin 15) :
            (m (class2LayerIndex true f)).1 = 0 := by
          simpa using hother f
        simp_rw [hz]
        rw [class2LayerNeighbourSum_eq_full]
        simp


end E7FourEightGenericData
end SRG266
