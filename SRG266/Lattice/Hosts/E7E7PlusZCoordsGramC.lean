/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Hosts.E7E7PlusZDefinitions

/-! # Bounded coordinate Gram rows 8--11 of the rank-15 E7 host -/

namespace SRG266
namespace Lattice

theorem e7e7PlusZCoords_gram_row_8 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 8 j =
      4 ^ 2 * e7e7PlusZGram 8 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZCoords_gram_row_9 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 9 j =
      4 ^ 2 * e7e7PlusZGram 9 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZCoords_gram_row_10 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 10 j =
      4 ^ 2 * e7e7PlusZGram 10 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZCoords_gram_row_11 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 11 j =
      4 ^ 2 * e7e7PlusZGram 11 j := by
  fin_cases j <;> decide +kernel

end Lattice
end SRG266

