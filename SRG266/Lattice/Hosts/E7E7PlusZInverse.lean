/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Hosts.E7E7PlusZInverseA
import SRG266.Lattice.Hosts.E7E7PlusZInverseB
import SRG266.Lattice.Hosts.E7E7PlusZInverseC
import SRG266.Lattice.Hosts.E7E7PlusZInverseD

namespace SRG266
namespace Lattice

theorem e7e7PlusZGram_mul_inv : e7e7PlusZGram * e7e7PlusZGramInv = 1 := by
  ext i j
  fin_cases i
  · exact e7e7PlusZGram_mul_inv_row_0 j
  · exact e7e7PlusZGram_mul_inv_row_1 j
  · exact e7e7PlusZGram_mul_inv_row_2 j
  · exact e7e7PlusZGram_mul_inv_row_3 j
  · exact e7e7PlusZGram_mul_inv_row_4 j
  · exact e7e7PlusZGram_mul_inv_row_5 j
  · exact e7e7PlusZGram_mul_inv_row_6 j
  · exact e7e7PlusZGram_mul_inv_row_7 j
  · exact e7e7PlusZGram_mul_inv_row_8 j
  · exact e7e7PlusZGram_mul_inv_row_9 j
  · exact e7e7PlusZGram_mul_inv_row_10 j
  · exact e7e7PlusZGram_mul_inv_row_11 j
  · exact e7e7PlusZGram_mul_inv_row_12 j
  · exact e7e7PlusZGram_mul_inv_row_13 j
  · exact e7e7PlusZGram_mul_inv_row_14 j

end Lattice
end SRG266

