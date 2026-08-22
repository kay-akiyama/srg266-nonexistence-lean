/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusZDefinitions

/-! # Bounded coordinate Gram rows 12--14 of the rank-15 E7 host -/

namespace SRG266
namespace Lattice

theorem e7e7PlusZCoords_gram_row_12 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 12 j =
      4 ^ 2 * e7e7PlusZGram 12 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZCoords_gram_row_13 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 13 j =
      4 ^ 2 * e7e7PlusZGram 13 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZCoords_gram_row_14 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 14 j =
      4 ^ 2 * e7e7PlusZGram 14 j := by
  fin_cases j <;> decide +kernel

end Lattice
end SRG266

