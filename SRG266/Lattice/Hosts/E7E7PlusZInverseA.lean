/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Hosts.E7E7PlusZDefinitions

/-! # Bounded inverse rows 0--3 of the rank-15 E7 host -/

namespace SRG266
namespace Lattice

theorem e7e7PlusZGram_mul_inv_row_0 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 0 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 0 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZGram_mul_inv_row_1 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 1 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 1 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZGram_mul_inv_row_2 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 2 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 2 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZGram_mul_inv_row_3 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 3 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 3 j := by
  fin_cases j <;> decide +kernel

end Lattice
end SRG266

