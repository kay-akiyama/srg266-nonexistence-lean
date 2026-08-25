/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.CherryBoundary
import SRG266.Certificates.FractionalNearFrame.Closed

/-!
# Pure Lean nonexistence of `srg(266,45,0,9)`

The exact fractional near-frame audit supplies the final combinatorial input to
the lattice and graph-theoretic proof.
-/

namespace SRG266

universe u

/-- There is no strongly regular graph with parameters `(266,45,0,9)`. -/
theorem srg266_nonexistence
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬ G.IsSRGWith 266 45 0 9 :=
  srg266_nonexistence_of_noResidualCherryCover
    QuasiSymmetric.noResidualCherryCover_holds G

end SRG266
