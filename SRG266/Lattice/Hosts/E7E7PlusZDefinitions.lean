/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusTrace
import SRG266.Certificates.E7E7PlusZGramData

/-!
# The host E7E7PlusZ certificate

The glued E7 core and its trace vectors are factored into lightweight
prerequisite modules; this file contains the adjoining rank-one host model.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators Matrix

/-! ## The host `(E₇ ⊕ E₇)⁺ ⊕ ℤ` -/

/-- Index of the host model: one `ℤ` coordinate and the two `E₇` factors. -/
abbrev E7E7PlusZIndex := Fin 1 ⊕ E7E7PlusIndex

/-- Linear position of a host coordinate in the generated data. -/
def e7e7PlusZPosition : E7E7PlusZIndex → ℕ :=
  Sum.elim (fun _ => 0) (fun k => 1 + e7e7PlusPosition k)

/-- Gram matrix of the generated basis of `(E₇ ⊕ E₇)⁺ ⊕ ℤ`. -/
def e7e7PlusZGram : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => (e7e7PlusZGramData.getD i.1 #[]).getD j.1 0

/-- Inverse of `e7e7PlusZGram`. -/
def e7e7PlusZGramInv : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => (e7e7PlusZGramInvData.getD i.1 #[]).getD j.1 0

/-- Lower factor of the LDLᵀ certificate of `e7e7PlusZGram`. -/
def e7e7PlusZLdltFactor : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => (e7e7PlusZLdltFactorData.getD i.1 #[]).getD j.1 0

/-- Weights of the LDLᵀ certificate of `e7e7PlusZGram`. -/
def e7e7PlusZLdltWeight : Fin 15 → ℤ :=
  fun k => e7e7PlusZLdltWeightData.getD k.1 0

/-- Basis of `(E₇ ⊕ E₇)⁺ ⊕ ℤ` in model coordinates, scaled by `4`. -/
def e7e7PlusZCoords : Matrix (Fin 15) E7E7PlusZIndex ℤ :=
  fun i j => (e7e7PlusZCoordsData.getD i.1 #[]).getD (e7e7PlusZPosition j) 0

/-- The `(E₇ ⊕ E₇)⁺` block of the coordinate matrix. -/
def e7e7PlusZPair : Matrix (Fin 15) E7E7PlusIndex ℤ :=
  fun i j => e7e7PlusZCoords i (Sum.inr j)

end Lattice
end SRG266

