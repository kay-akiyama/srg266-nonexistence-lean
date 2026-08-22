/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7E7PlusGramData
import SRG266.Lattice.HostCertificate

/-!
# The core `(E₇ ⊕ E₇)⁺` and the host `(E₇ ⊕ E₇)⁺ ⊕ ℤ`

Both lattices are presented with scale `4`: `4 • (E₇ ⊕ E₇)⁺` is the glued pair model
`SRG266.Lattice.gluedPairSubmodule` on `8 + 8` coordinates, and the host adds a
`ℤ` block, whose scaled coordinate is a multiple of `4`.

* `SRG266.Lattice.e7e7Plus_norm_three_iff` — the `3136`
  norm-three vectors of the core are exactly the pairs of minimal vectors of
  `E₇* ∖ E₇`, that is of minuscule weights;
* `SRG266.Lattice.e7e7PlusZHost : SRG266.OddUnimodularLattice15`;
* `SRG266.Lattice.e7e7PlusZ_norm_three_iff` — the `3640` norm-three vectors of
  the host are those `3136` together with the `504` sums of an `E₇ ⊕ E₇` root
  and a unit vector of `ℤ`.

Two further sections provide the branch construction.

* `SRG266.Lattice.e7e7Plus_even_block_of_even_norm` — a core vector of even norm
  lies in `E₇ ⊕ E₇` rather than the glue coset, because a glue-coset block has
  square sum `24` modulo `32` and two of them add up to `16`, never `0`.
* `SRG266.Lattice.e7e7PlusTraceCoeff` — lattice coefficients of the eight
  vectors `8 e_i - 1 ∈ A₇` of one factor, at which the projector bound produces
  the trace filter.  Like the doubled units of `D₁₂⁺` they need no new
  certificate data: `Coordsᵀ * Gram⁻¹` is the scaled left inverse of the
  coordinate presentation, and the kernel re-checks the resulting coefficients.
-/

namespace SRG266
namespace Lattice

open Finset

set_option maxRecDepth 8000

/-! ## The core `(E₇ ⊕ E₇)⁺` -/

/-- Index of the core model: the two `E₇` factors. -/
abbrev E7E7PlusIndex := Fin 8 ⊕ Fin 8

/-- Linear position of a core coordinate in the generated data. -/
def e7e7PlusPosition : E7E7PlusIndex → ℕ :=
  Sum.elim (fun k => k.1) (fun k => 8 + k.1)

/-- Gram matrix of the generated basis of `(E₇ ⊕ E₇)⁺`. -/
def e7e7PlusGram : Matrix (Fin 14) (Fin 14) ℤ :=
  fun i j => (e7e7PlusGramData.getD i.1 #[]).getD j.1 0

/-- Inverse of `e7e7PlusGram`. -/
def e7e7PlusGramInv : Matrix (Fin 14) (Fin 14) ℤ :=
  fun i j => (e7e7PlusGramInvData.getD i.1 #[]).getD j.1 0

/-- Lower factor of the LDLᵀ certificate of `e7e7PlusGram`. -/
def e7e7PlusLdltFactor : Matrix (Fin 14) (Fin 14) ℤ :=
  fun i j => (e7e7PlusLdltFactorData.getD i.1 #[]).getD j.1 0

/-- Weights of the LDLᵀ certificate of `e7e7PlusGram`. -/
def e7e7PlusLdltWeight : Fin 14 → ℤ :=
  fun k => e7e7PlusLdltWeightData.getD k.1 0

/-- Basis of `(E₇ ⊕ E₇)⁺` in model coordinates, scaled by `4`. -/
def e7e7PlusCoords : Matrix (Fin 14) E7E7PlusIndex ℤ :=
  fun i j => (e7e7PlusCoordsData.getD i.1 #[]).getD (e7e7PlusPosition j) 0

end Lattice
end SRG266
