/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.FrameCore
import SRG266.Lattice.Hosts.A15Plus
import SRG266.Lattice.Hosts.D12PlusZ3
import SRG266.Lattice.Hosts.E7E7PlusZ

/-!
# The lightweight corank-four classification statement

This module isolates the statement used by
`SRG266.Lattice.KneserBoundary`.  Keeping the proposition independent of the
host-dispatch and shell-certificate modules lets alternative proofs of the
classification boundary compile without loading those large developments.
-/

namespace SRG266

/-- A positive-definite unimodular lattice of rank twelve through fifteen with
no vector of norm one is one of the three standard coordinate models.

`SRG266.Lattice.KneserBoundary` proves that this proposition supplies the
rooted host-classification input. -/
abbrev RootedCorankFourClassification : Prop :=
  ∀ (n₀ : ℕ), 12 ≤ n₀ → n₀ ≤ 15 → ∀ (L : PDUnimodularLattice n₀),
    (∀ v : L.carrier, L.pairing v v ≠ 1) →
      Lattice.IsMatrixModel L Lattice.d12PlusGram ∨
        Lattice.IsMatrixModel L Lattice.e7e7PlusGram ∨
        Lattice.IsMatrixModel L Lattice.a15PlusGram

end SRG266
