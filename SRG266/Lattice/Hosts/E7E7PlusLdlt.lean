/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Hosts.E7E7PlusDefinitions

namespace SRG266
namespace Lattice

theorem e7e7PlusGram_ldlt :
    checkIntegerScaledGram e7e7PlusGram e7e7PlusLdltFactor e7e7PlusLdltWeight
      e7e7PlusLdltScale = true := by
  apply checkIntegerScaledGram_of_rows
  intro i
  fin_cases i <;> decide +kernel

end Lattice
end SRG266
