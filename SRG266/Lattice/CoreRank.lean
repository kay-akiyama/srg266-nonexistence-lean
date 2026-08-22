/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.PositiveDefinite
import SRG266.NormOneDirections
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# The corank lemma: the norm-one-free core has rank at least twelve

A pure embedding of the local Gram lattice into a rank-15 host puts a rank-12
sublattice inside the orthogonal complement of *every* norm-one direction.  So
a maximal orthonormal family `u : Fin k → L` inside such a host has `k ≤ 3`,
and the norm-one-free core `L₀ = u^⊥`, of rank `n₀ = 15 - k`, has rank at
least twelve.

The three steps.

* The rank of the abstract Gram lattice is already in the repository:
  `SRG266.Lattice.finrank_integralGramLattice`
  (`SRG266/Lattice/PositiveDefinite.lean`) reads `220 - 208 = 12` off the
  rank-208 radical of `SRG266/KernelRank.lean`.  What is added here is that
  the same lattice is *free*: it is torsion-free because the generator profile
  `SRG266.Lattice.integralGramProfile` is injective, and finitely generated
  because it is a quotient, so the structure theorem over a principal ideal
  domain applies.  Freeness is what lets `Module.finrank_prod` split the rank
  of the domain of the injection below.
* `SRG266.Lattice.pairing_embedding_eq_zero`: purity —
  `SRG266.Rank15EmbeddingWitness.NormOneDirectionsOrthogonal`, which speaks
  only about the `220` distinguished generators — extends to the whole
  embedded lattice, because those generators span it.
* `SRG266.Lattice.card_normOne_le_three`: the coproduct of the embedding with
  the orthonormal family is injective, so `12 + k ≤ 15`.

Injectivity is where the two hypotheses meet: pairing the relation
`E.embedding p + ∑ aᵢ uᵢ = 0` with `u j` kills the embedded part by purity and
reads off `a j` by orthonormality.

`SRG266.Lattice.twelve_le_coreRank` is the design's own phrasing `12 ≤ n₀`.
Its consumer is `SRG266/Lattice/KneserBoundary.lean`, where it becomes the
rank hypothesis of `SRG266.RootedNormOneFreeClassification` and thereby
deletes the two rank-deficient rows — the zero core and the `E₈` core — from
that statement's conclusion.
-/

open scoped BigOperators

namespace SRG266
namespace Lattice

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## The abstract Gram lattice is free of rank twelve -/

/-- The profile of a lattice element against the `220` distinguished
generators.  It separates points (`SRG266.integralGram_eq_of_pairing_generators_eq`),
which is all that is needed to see that the quotient is torsion-free. -/
def integralGramProfile (x : V) :
    IntegralGramLattice G x →ₗ[ℤ] (SecondSubconstituent G x → ℤ) :=
  LinearMap.pi fun B => (integralGramPairing G x).flip (integralGramGenerator G x B)

@[simp]
theorem integralGramProfile_apply (x : V) (p : IntegralGramLattice G x)
    (B : SecondSubconstituent G x) :
    integralGramProfile G x p B =
      integralGramPairing G x p (integralGramGenerator G x B) := rfl

theorem integralGramProfile_injective (x : V) :
    Function.Injective (integralGramProfile G x) := by
  intro p q h
  exact integralGram_eq_of_pairing_generators_eq G x p q fun B => congrFun h B

/-- The abstract Gram lattice is torsion-free: it embeds in a free module by
its generator profile. -/
instance integralGramLattice_isTorsionFree (x : V) :
    Module.IsTorsionFree ℤ (IntegralGramLattice G x) :=
  Function.Injective.moduleIsTorsionFree _ (integralGramProfile_injective G x)
    fun r p => LinearMap.map_smul (integralGramProfile G x) r p

/-- The abstract Gram lattice is a finitely generated `ℤ`-module: it is a
quotient of the free module on the `220` blocks.  Together with the previous
instance this makes it free, by the structure theorem over a principal ideal
domain. -/
instance integralGramLattice_finite (x : V) :
    Module.Finite ℤ (IntegralGramLattice G x) :=
  Module.Finite.of_surjective (integralGramRelations G x).mkQ
    (Submodule.mkQ_surjective _)

/-! ## Purity extends from the generators to the embedded lattice -/

/-- **Purity is a statement about the whole embedded lattice.**  The `220`
distinguished generators span `SRG266.IntegralGramLattice`, so a norm-one host
direction orthogonal to all of them is orthogonal to every embedded vector. -/
theorem pairing_embedding_eq_zero {x : V} (E : Rank15EmbeddingWitness G x)
    (hpure : E.NormOneDirectionsOrthogonal G) {u : E.host.carrier}
    (hu : E.host.pairing u u = 1) (p : IntegralGramLattice G x) :
    E.host.pairing u (E.embedding p) = 0 := by
  classical
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (integralGramRelations G x) p
  rw [mk_eq_sum_smul_generator G x z, map_sum, map_sum]
  refine Finset.sum_eq_zero fun B _ => ?_
  rw [LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul]
  have hB : E.host.pairing u (E.embeddedGenerator (G := G) B) = 0 := hpure u hu B
  rw [show E.embedding (integralGramGenerator G x B) =
    E.embeddedGenerator (G := G) B from rfl, hB, mul_zero]

/-! ## The corank lemma -/

/-- In a pure embedding the orthonormal
family split off the host has at most three members.

The embedded Gram lattice has rank twelve and lies in the orthogonal
complement of every norm-one direction, so it is independent of the family;
the host has rank fifteen. -/
theorem card_normOne_le_three {x : V} (hG : IsHypothetical G)
    (E : Rank15EmbeddingWitness G x) (hpure : E.NormOneDirectionsOrthogonal G)
    {k : ℕ} {u : Fin k → E.host.carrier}
    (hnorm : ∀ i, E.host.pairing (u i) (u i) = 1)
    (horth : ∀ i j, i ≠ j → E.host.pairing (u i) (u j) = 0) :
    k ≤ 3 := by
  classical
  haveI := E.host.moduleFree
  haveI := E.host.moduleFinite
  set φ : (IntegralGramLattice G x) × (Fin k → ℤ) →ₗ[ℤ] E.host.carrier :=
    E.embedding.coprod (Fintype.linearCombination ℤ u) with hφ
  have hcombination : ∀ (a : Fin k → ℤ) (j : Fin k),
      E.host.pairing (u j) (Fintype.linearCombination ℤ u a) = a j := by
    intro a j
    rw [Fintype.linearCombination_apply, map_sum, Finset.sum_eq_single j]
    · rw [LinearMap.map_smul, smul_eq_mul, hnorm j, mul_one]
    · intro i _ hij
      rw [LinearMap.map_smul, smul_eq_mul, horth j i (Ne.symm hij), mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨p, a⟩ hpa
    have hvalue : E.embedding p + Fintype.linearCombination ℤ u a = 0 := hpa
    have hzero : ∀ j, a j = 0 := by
      intro j
      have hj : E.host.pairing (u j)
          (E.embedding p + Fintype.linearCombination ℤ u a) = 0 := by
        rw [hvalue, map_zero]
      rw [map_add, pairing_embedding_eq_zero G E hpure (hnorm j) p, zero_add,
        hcombination a j] at hj
      exact hj
    have ha : a = 0 := funext hzero
    subst ha
    rw [map_zero, add_zero] at hvalue
    have hp : p = 0 := E.injective (by rw [hvalue, map_zero])
    simp [hp]
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod, finrank_integralGramLattice G hG x,
    Module.finrank_fin_fun ℤ, E.host.rank] at hle
  omega

/-- **`12 ≤ n₀`.**  The design's phrasing of `SRG266.Lattice.card_normOne_le_three`:
the norm-one-free core `u^⊥` of a purely embedded host has rank at least
twelve. -/
theorem twelve_le_coreRank {x : V} (hG : IsHypothetical G)
    (E : Rank15EmbeddingWitness G x) (hpure : E.NormOneDirectionsOrthogonal G)
    {k : ℕ} {u : Fin k → E.host.carrier}
    (hnorm : ∀ i, E.host.pairing (u i) (u i) = 1)
    (horth : ∀ i j, i ≠ j → E.host.pairing (u i) (u j) = 0) :
    12 ≤ 15 - k := by
  have := card_normOne_le_three G hG E hpure hnorm horth
  omega

end Lattice
end SRG266
