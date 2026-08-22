/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Hosts.E7E7PlusZDefinitions

/-! # Bounded coordinate Gram rows 4--7 of the rank-15 E7 host -/

namespace SRG266
namespace Lattice

theorem e7e7PlusZCoords_gram_row_4 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 4 j =
      4 ^ 2 * e7e7PlusZGram 4 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZCoords_gram_row_5 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 5 j =
      4 ^ 2 * e7e7PlusZGram 5 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZCoords_gram_row_6 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 6 j =
      4 ^ 2 * e7e7PlusZGram 6 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZCoords_gram_row_7 (j : Fin 15) :
    (e7e7PlusZCoords * e7e7PlusZCoords.transpose) 7 j =
      4 ^ 2 * e7e7PlusZGram 7 j := by
  fin_cases j <;> decide +kernel

end Lattice
end SRG266

