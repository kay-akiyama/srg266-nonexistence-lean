/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusTraceCheckFalse
import SRG266.Lattice.Hosts.E7E7PlusTraceCheckTrue

/-! # Exact presentation check for the E7 trace vectors -/

namespace SRG266
namespace Lattice

theorem e7e7PlusTraceCoeff_vecMul :
    ∀ (side : Bool) (i : Fin 8) (j : E7E7PlusIndex),
      Matrix.vecMul (e7e7PlusTraceCoeff side i) e7e7PlusCoords j =
        e7e7PlusTraceVector side i j := by
  intro side i j
  cases side
  · exact e7e7PlusTraceCoeff_vecMul_false i j
  · exact e7e7PlusTraceCoeff_vecMul_true i j

end Lattice
end SRG266
