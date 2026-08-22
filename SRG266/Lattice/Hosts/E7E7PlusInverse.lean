/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Hosts.E7E7PlusDefinitions

namespace SRG266
namespace Lattice

theorem e7e7PlusGram_mul_inv : e7e7PlusGram * e7e7PlusGramInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

end Lattice
end SRG266
