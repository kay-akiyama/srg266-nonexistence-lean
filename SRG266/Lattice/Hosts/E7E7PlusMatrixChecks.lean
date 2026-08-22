/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusSymmetry
import SRG266.Lattice.Hosts.E7E7PlusInverse
import SRG266.Lattice.Hosts.E7E7PlusLdlt
import SRG266.Lattice.Hosts.E7E7PlusCoordsGram

/-! # Exact matrix checks for the glued E7 core -/

namespace SRG266
namespace Lattice

theorem e7e7PlusGram_posDef :
    ∀ v : Fin 14 → ℤ, v ≠ 0 → 0 < Matrix.toBilin' e7e7PlusGram v v :=
  toBilin'_posDef_of_ldlt e7e7PlusGram e7e7PlusGramInv e7e7PlusLdltFactor
    e7e7PlusLdltWeight e7e7PlusLdltScale e7e7PlusGram_isSymm e7e7PlusGram_mul_inv
    e7e7PlusGram_ldlt

end Lattice
end SRG266
