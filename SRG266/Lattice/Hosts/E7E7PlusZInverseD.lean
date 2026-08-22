/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusZDefinitions

/-! # Bounded inverse rows 12--14 of the rank-15 E7 host -/

namespace SRG266
namespace Lattice

theorem e7e7PlusZGram_mul_inv_row_12 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 12 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 12 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZGram_mul_inv_row_13 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 13 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 13 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZGram_mul_inv_row_14 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 14 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 14 j := by
  fin_cases j <;> decide +kernel

end Lattice
end SRG266

