/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Branches.PureCoreModel
import SRG266.NormOneDirections

/-!
# Construction of pure core models

This module builds the lightweight coordinate model from a classified
norm-one-free host core.  The model structure and its coordinate lemmas live
in `SRG266.Lattice.Branches.PureCoreModel`.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the pure case every embedded generator is orthogonal to every norm-one
host vector. The centroid is also orthogonal because `11 • c` is the generator
sum and `ℤ` is torsion free. -/
theorem PureCoreModel.exists_of_isHostCoreModel {x : V} (E : Rank15EmbeddingWitness G x)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (hpure : E.NormOneDirectionsOrthogonal G) {k : ℕ} {u : Fin k → E.host.carrier}
    (hu : ∀ i, E.host.pairing (u i) (u i) = 1)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hmodel : IsHostCoreModel E.host u A) :
    Nonempty (PureCoreModel E c A) := by
  classical
  obtain ⟨f, hf, hcover⟩ := hmodel
  have hgen : ∀ B : SecondSubconstituent G x,
      ∃ v, f v = E.embeddedGenerator (G := G) B := by
    intro B
    exact hcover _ fun i => hpure (u i) (hu i) B
  have hcen : ∃ v, f v = E.embeddedCentroid (G := G) c := by
    refine hcover _ fun i => ?_
    have hsum := E.directionProfile_sum (G := G) c hc (u i)
    have hzero : ∑ B, E.directionProfile (G := G) (u i) B = 0 :=
      Finset.sum_eq_zero fun B _ => hpure (u i) (hu i) B
    rw [hzero] at hsum
    have : E.centroidCoordinate (G := G) c (u i) = 0 := by omega
    exact this
  choose gen hgen using hgen
  obtain ⟨cen, hcen⟩ := hcen
  exact ⟨{ coords := f
           pairing_coords := hf
           generator := gen
           coords_generator := hgen
           centroid := cen
           coords_centroid := hcen }⟩

end Lattice
end SRG266
