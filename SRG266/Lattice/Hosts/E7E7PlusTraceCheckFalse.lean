/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Hosts.E7E7PlusTraceDefinitions

namespace SRG266
namespace Lattice

theorem e7e7PlusTraceCoeff_vecMul_false :
    ∀ (i : Fin 8) (j : E7E7PlusIndex),
      Matrix.vecMul (e7e7PlusTraceCoeff false i) e7e7PlusCoords j =
        e7e7PlusTraceVector false i j := by
  decide +kernel

end Lattice
end SRG266
