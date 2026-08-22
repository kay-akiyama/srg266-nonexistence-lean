/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Branches.A15MinedShellFactsData

/-! # Generator shell facts for the mined A15 construction -/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Extract the generator shell identities from a pure A15 core. -/
theorem a15MinedShellFacts_of_pureCoreModel {x : V}
    (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c a15PlusGram) :
    ∃ S : A15MinedShellFacts (G := G) x,
      S.centroid = Matrix.vecMul M.centroid a15PlusCoords := by
  classical
  set y : SecondSubconstituent G x → Fin 16 → ℤ :=
    fun B => Matrix.vecMul (M.generator B) a15PlusCoords with hyDef
  set d : Fin 16 → ℤ := Matrix.vecMul M.centroid a15PlusCoords with hdDef
  have hnorm3 : ∀ B, ∃ S : Finset (Fin 16), S.card = 4 ∧
      ((∀ j, y B j = if j ∈ S then -3 else 1) ∨
        (∀ j, y B j = if j ∈ S then 3 else -1)) := fun B =>
    (a15Plus_norm_three_iff (M.generator B)).mp (M.generator_norm hG B)
  choose S hScard hSshell using hnorm3
  have hpair : ∀ B, ∑ i, d i * y B i = 240 := by
    intro B
    have h := dotProduct_vecMul_coords a15PlusGram a15PlusCoords 4
      a15PlusCoords_gram M.centroid (M.generator B)
    rw [M.centroid_generator hG hc, dotProduct] at h
    have h' : ∑ i, d i * y B i = 4 ^ 2 * 15 := h
    linarith
  have hgram : ∀ B C, ∑ i, y B i * y C i =
      16 * localGramMatrix G x B C := by
    intro B C
    have h := dotProduct_vecMul_coords a15PlusGram a15PlusCoords 4
      a15PlusCoords_gram (M.generator B) (M.generator C)
    rw [M.gram B C, dotProduct] at h
    have h' : ∑ i, y B i * y C i =
        4 ^ 2 * localGramMatrix G x B C := h
    rw [h']
    ring
  have hgensum : ∀ k, ∑ B, M.generator B k = 11 * M.centroid k := by
    intro k
    have h := congrFun (M.generator_sum a15PlusGram_posDef hc) k
    rw [Finset.sum_apply] at h
    simpa using h
  have hcent : ∀ i, ∑ B, y B i = 11 * d i := by
    intro i
    have hexpY : ∀ B, y B i =
        ∑ k, M.generator B k * a15PlusCoords k i := fun B => by
      simp [hyDef, Matrix.vecMul, dotProduct]
    have hexpD : d i = ∑ k, M.centroid k * a15PlusCoords k i := by
      simp [hdDef, Matrix.vecMul, dotProduct]
    rw [Finset.sum_congr rfl fun B _ => hexpY B, Finset.sum_comm,
      hexpD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, hgensum k]
    ring
  refine ⟨{
    centroid := d
    generator := y
    support := S
    centroid_sum := (a15Plus_vecMul_mem M.centroid).1
    support_card := hScard
    shell := hSshell
    centroid_pair := hpair
    gram := hgram
    generator_sum := hcent
  }, ?_⟩
  rfl

end Lattice
end SRG266
