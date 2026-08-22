/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusZDefinitions

/-! # Bounded inverse rows 8--11 of the rank-15 E7 host -/

namespace SRG266
namespace Lattice

theorem e7e7PlusZGram_mul_inv_row_8 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 8 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 8 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZGram_mul_inv_row_9 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 9 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 9 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZGram_mul_inv_row_10 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 10 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 10 j := by
  fin_cases j <;> decide +kernel

theorem e7e7PlusZGram_mul_inv_row_11 (j : Fin 15) :
    (e7e7PlusZGram * e7e7PlusZGramInv) 11 j = (1 : Matrix (Fin 15) (Fin 15) ℤ) 11 j := by
  fin_cases j <;> decide +kernel

end Lattice
end SRG266

