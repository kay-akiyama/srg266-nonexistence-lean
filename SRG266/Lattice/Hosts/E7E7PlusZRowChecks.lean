/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusZDefinitions

/-! # Bounded row checks for the rank-15 E7 host -/

namespace SRG266
namespace Lattice

open scoped BigOperators Matrix

theorem e7e7PlusZCoords_row_unit :
    ∀ (i : Fin 15) (j : Fin 1), e7e7PlusZCoords i (Sum.inl j) % 4 = 0 := by
  decide +kernel

theorem e7e7PlusZPair_row_left_sum : ∀ i : Fin 15, ∑ j, e7e7PlusZPair i (Sum.inl j) = 0 := by
  decide +kernel

theorem e7e7PlusZPair_row_right_sum : ∀ i : Fin 15, ∑ j, e7e7PlusZPair i (Sum.inr j) = 0 := by
  decide +kernel

theorem e7e7PlusZPair_row_left_congruent :
    ∀ (i : Fin 15) (j : Fin 8),
      e7e7PlusZPair i (Sum.inl j) % 4 = e7e7PlusZPair i (Sum.inl 0) % 4 := by
  decide +kernel

theorem e7e7PlusZPair_row_right_congruent :
    ∀ (i : Fin 15) (j : Fin 8),
      e7e7PlusZPair i (Sum.inr j) % 4 = e7e7PlusZPair i (Sum.inr 0) % 4 := by
  decide +kernel

theorem e7e7PlusZPair_row_glue :
    ∀ i : Fin 15,
      (e7e7PlusZPair i (Sum.inl 0) - e7e7PlusZPair i (Sum.inr 0)) % 2 = 0 := by
  decide +kernel

end Lattice
end SRG266
