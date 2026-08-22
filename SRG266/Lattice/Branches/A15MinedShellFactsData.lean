/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Branches.A15MinedCentroid

/-! # Data interface for mined A15 generator shell facts -/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Integer generator identities, independent of centroid canonicalization. -/
structure A15MinedShellFacts (x : V) where
  centroid : Fin 16 → ℤ
  generator : SecondSubconstituent G x → Fin 16 → ℤ
  support : SecondSubconstituent G x → Finset (Fin 16)
  centroid_sum : ∑ i, centroid i = 0
  support_card : ∀ B, (support B).card = 4
  shell : ∀ B,
    (∀ i, generator B i = if i ∈ support B then -3 else 1) ∨
      (∀ i, generator B i = if i ∈ support B then 3 else -1)
  centroid_pair : ∀ B, ∑ i, centroid i * generator B i = 240
  gram : ∀ B C, ∑ i, generator B i * generator C i =
    16 * localGramMatrix G x B C
  generator_sum : ∀ i, ∑ B, generator B i = 11 * centroid i

end Lattice
end SRG266
