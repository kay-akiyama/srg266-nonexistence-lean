/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Hosts.E7E7PlusZDefinitions

/-! # Bounded coordinate Gram rows 0--3 of the rank-15 E7 host -/

namespace SRG266
namespace Lattice

theorem e7e7PlusZCoords_gram_row_0 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 0 j =
      4 ^ 2 * e7e7PlusZGram 0 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZCoords_gram_row_1 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 1 j =
      4 ^ 2 * e7e7PlusZGram 1 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZCoords_gram_row_2 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 2 j =
      4 ^ 2 * e7e7PlusZGram 2 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZCoords_gram_row_3 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 3 j =
      4 ^ 2 * e7e7PlusZGram 3 j := by
  fin_cases j <;> decide +kernel

end Lattice
end SRG266

