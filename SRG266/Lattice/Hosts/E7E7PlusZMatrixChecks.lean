/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusZSymmetry
import SRG266.Lattice.Hosts.E7E7PlusZInverse
import SRG266.Lattice.Hosts.E7E7PlusZLdlt
import SRG266.Lattice.Hosts.E7E7PlusZCoordsGram

/-! # Matrix checks for the rank-15 E7 host -/

namespace SRG266
namespace Lattice

open scoped BigOperators Matrix

theorem e7e7PlusZGram_posDef :
    ∀ v : Fin 15 → ℤ, v ≠ 0 → 0 < Matrix.toBilin' e7e7PlusZGram v v :=
  toBilin'_posDef_of_ldlt e7e7PlusZGram e7e7PlusZGramInv e7e7PlusZLdltFactor
    e7e7PlusZLdltWeight e7e7PlusZLdltScale e7e7PlusZGram_isSymm e7e7PlusZGram_mul_inv
    e7e7PlusZGram_ldlt

end Lattice
end SRG266

