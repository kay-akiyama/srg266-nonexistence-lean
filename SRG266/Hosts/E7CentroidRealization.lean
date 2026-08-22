/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7E7Plus
import SRG266.GramMatrix

/-!
# Lightweight direct E7 centroid realizations

This module isolates the realization structure from the generated survivor
tables and the residual transport proofs.  Producers of a realization need
only this small interface; consumers can import `E7CentroidTransport` for the
derived counting and transport operations.
-/

open scoped BigOperators Matrix

namespace SRG266

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A direct realization in the paired minuscule shell at the integral
centroid-certificate scale. -/
structure E7CentroidShellGramRealization
    (x : V) (y₁ y₂ : Fin 8 → ℤ) where
  shell : SecondSubconstituent G x → E7EligibleIndex y₁ y₂
  gram :
    ∀ B C, e7ShellInner (shell B).1 (shell C).1 =
      localGramMatrix G x B C
  leftCentroid :
    ∀ i, ∑ B, e7Weight4 (shell B).1.1 i = 22 * y₁ i
  rightCentroid :
    ∀ i, ∑ B, e7Weight4 (shell B).1.2 i = 22 * y₂ i

end SRG266
