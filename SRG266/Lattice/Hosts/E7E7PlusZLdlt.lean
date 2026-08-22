/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusZDefinitions

/-! # LDLT check for the rank-15 E7 host -/

namespace SRG266
namespace Lattice

open scoped BigOperators Matrix

theorem e7e7PlusZGram_ldlt :
    checkIntegerScaledGram e7e7PlusZGram e7e7PlusZLdltFactor e7e7PlusZLdltWeight
      e7e7PlusZLdltScale = true := by
  apply checkIntegerScaledGram_of_rows
  intro i
  fin_cases i <;> decide +kernel

end Lattice
end SRG266

