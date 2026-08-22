/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.GlueHost
import SRG266.Lattice.GramOverlattice

/-!
# The Yang--Yoshino rank-15 embedding, proved

This module feeds the graph-side data of `SRG266/Lattice/GramOverlattice.lean`
into the graph-independent glue
machine of `SRG266/Lattice/GlueHost.lean`.

For a hypothetical `srg(266, 45, 0, 9)` and a vertex `x`:

* `ratGramSpace G x` is a `12`-dimensional rational quadratic space
  (`finrank_ratGramSpace`) whose form is positive definite
  (`ratGramForm_posDef`);
* `gramLattice G x` is an integral lattice in it (`gramLattice_isLattice`,
  `gramLattice_isIntegral`) with `225 • Λ^∨ ⊆ Λ` (`gram_dual_denominator`);
* a maximal integral overlattice `Λ̃` exists whose dual has squarefree
  denominator `15` (`nonempty_maximalGramOverlattice`), and its discriminant
  datum is at most two glue vectors at `3` together with at most two at `5`
  (`MaximalGramOverlattice.exists_glueBases`);
* the certificate table of `SRG266/Certificates/Rank15ComplementData.lean`
  supplies a rank-`3` complement for that datum, and the glue construction
  produces a positive-definite odd unimodular lattice of rank `15` containing
  `Λ̃` isometrically (`exists_host_of_glueBases`).

Oddness of the host comes from the diagonal of the local Gram matrix: every
generator has norm `3` (`localGramMatrix_diagonal`).

The two exported results are `SRG266.exists_rank15_embedding` and the
instance-level discharge

```lean
theorem yangYoshinoRank15Embedding : YangYoshinoRank15Embedding.{u}
```

`SRG266.yangYoshinoRank15Embedding` supplies the corresponding conditional
theorem input.
-/

namespace SRG266

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A vector of odd norm -/

/-- Every local Gram generator has norm `3`, so the Gram lattice contains a
vector of odd norm.  This is what makes the glued rank-15 host *odd*. -/
theorem exists_odd_norm_mem_gramLattice (hG : IsHypothetical G) (x : V) :
    ∃ z ∈ gramLattice G x, ∃ k : ℤ, ¬ Even k ∧ (k : ℚ) = ratGramForm G x z z := by
  haveI : Nonempty (SecondSubconstituent G x) :=
    Fintype.card_pos_iff.mp (by rw [secondSubconstituent_card G hG x]; norm_num)
  obtain ⟨B⟩ : Nonempty (SecondSubconstituent G x) := inferInstance
  have hnorm :
      ratGramForm G x (toRatSpace G x (integralGramGenerator G x B))
          (toRatSpace G x (integralGramGenerator G x B)) = ((3 : ℤ) : ℚ) := by
    rw [toRatSpace_pairing, integralGramPairing_generator_generator,
      localGramMatrix_diagonal G hG x B]
  exact ⟨toRatSpace G x (integralGramGenerator G x B),
    toRatSpace_mem_gramLattice G x _, 3, by norm_num, hnorm.symm⟩

/-! ## The Gram lattice inside a maximal overlattice -/

/-- The abstract integral Gram lattice maps into any maximal integral
overlattice of its image. -/
def gramToOverlattice {x : V} (Λ : MaximalGramOverlattice G x) :
    IntegralGramLattice G x →ₗ[ℤ] Λ.carrier :=
  LinearMap.codRestrict Λ.carrier (toRatSpace G x)
    fun a => Λ.gramLattice_le (toRatSpace_mem_gramLattice G x a)

@[simp]
theorem gramToOverlattice_coe {x : V} (Λ : MaximalGramOverlattice G x)
    (a : IntegralGramLattice G x) :
    ((gramToOverlattice G Λ a : Λ.carrier) : ratGramSpace G x) =
      toRatSpace G x a := rfl

theorem gramToOverlattice_injective {x : V} (Λ : MaximalGramOverlattice G x) :
    Function.Injective (gramToOverlattice G Λ) := by
  intro a b hab
  refine toRatSpace_injective G x ?_
  rw [← gramToOverlattice_coe G Λ a, ← gramToOverlattice_coe G Λ b, hab]

/-! ## Assembly -/

/-- **The Yang--Yoshino embedding theorem for the local Gram lattice.**  The
rank-12 local integral Gram lattice of a hypothetical `srg(266, 45, 0, 9)`
embeds, preserving the pairing, into a positive-definite odd unimodular
integral lattice of rank 15. -/
theorem exists_rank15_embedding (hG : IsHypothetical G) (x : V) :
    Nonempty (Rank15EmbeddingWitness G x) := by
  classical
  obtain ⟨Λ⟩ := nonempty_maximalGramOverlattice G hG x
  obtain ⟨S, T, hsplit⟩ := Λ.exists_glueBases hG
  obtain ⟨z, hz, k, hk, hkz⟩ := exists_odd_norm_mem_gramLattice G hG x
  obtain ⟨L, e, hinj, hpair⟩ :=
    exists_host_of_glueBases (ratGramForm_isSymm G x) (ratGramForm_posDef G hG x)
      (finrank_ratGramSpace G hG x) Λ.isLattice Λ.isMaximal.integral S T hsplit
      ⟨z, Λ.gramLattice_le hz, k, hk, hkz⟩
  refine ⟨{ host := L
            embedding := e ∘ₗ gramToOverlattice G Λ
            injective := hinj.comp (gramToOverlattice_injective G Λ)
            preservesPairing := ?_ }⟩
  intro a b
  have h := hpair (gramToOverlattice G Λ a) (gramToOverlattice G Λ b)
  rw [gramToOverlattice_coe, gramToOverlattice_coe, toRatSpace_pairing] at h
  exact_mod_cast h

/-- The local Gram lattice embeds in a rank-15 odd unimodular lattice. -/
theorem yangYoshinoRank15Embedding : YangYoshinoRank15Embedding.{u} := by
  intro V _ _ G _ hG x
  exact exists_rank15_embedding G hG x

end SRG266
