/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Hosts.E7E7PlusZDefinitions

/-! # Bounded inverse rows 4--7 of the rank-15 E7 host -/

namespace SRG266
namespace Lattice

theorem e7e7PlusZGram_mul_inv_row_4 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 4 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 4 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZGram_mul_inv_row_5 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 5 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 5 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZGram_mul_inv_row_6 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 6 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 6 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZGram_mul_inv_row_7 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 7 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 7 j := by
  fin_cases j <;> decide +kernel

end Lattice
end SRG266

