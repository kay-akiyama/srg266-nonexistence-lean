/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Branches.E7ConstructionArithmetic

/-! # Raw coordinate blocks for the pure E7 branch -/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

set_option maxRecDepth 40000

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Generator and centroid coordinate blocks before parity reduction. -/
structure E7RawConstructionData {x : V}
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (M : PureCoreModel E c e7e7PlusGram) where
  Y : SecondSubconstituent G x → Bool → Fin 8 → ℤ
  D : Bool → Fin 8 → ℤ
  Y_eq : ∀ B side i, Y B side i = e7e7PlusBlock side (M.generator B) i
  D_eq : ∀ side i, D side i = e7e7PlusBlock side M.centroid i
  D_five : ∀ side i, (5 : ℤ) ∣ D side i
  subconstituent_card :
    (Finset.univ : Finset (SecondSubconstituent G x)).card = 220
  Y_minimal : ∀ B side, IsE7Minimal (Y B side)
  Y_sq : ∀ B side, ∑ i, (Y B side i) ^ 2 = 24
  D_sum : ∀ side, ∑ i, D side i = 0
  D_residue : ∀ side, ∃ r : ℤ,
    (2 : ℤ) ∣ r ∧ ∀ i, (4 : ℤ) ∣ (D side i - r)

/-- Extract the coordinate blocks and their common residue. -/
theorem e7RawConstructionData_of_pureCoreModel {x : V}
    (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c e7e7PlusGram) :
    Nonempty (E7RawConstructionData M) := by
  classical
  obtain ⟨Y, hY⟩ : ∃ Y : SecondSubconstituent G x → Bool → Fin 8 → ℤ,
      ∀ B side i, Y B side i = e7e7PlusBlock side (M.generator B) i :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Bool → Fin 8 → ℤ,
      ∀ side i, D side i = e7e7PlusBlock side M.centroid i := ⟨_, fun _ _ => rfl⟩
  have hDfive : ∀ side i, (5 : ℤ) ∣ D side i := by
    intro side i
    rw [hD side i]
    exact e7e7Plus_centroid_block_five_dvd hG hc M side i
  have hcard : (Finset.univ : Finset (SecondSubconstituent G x)).card = 220 := by
    rw [Finset.card_univ]
    exact secondSubconstituent_card G hG x
  -- Every generator block is a minuscule weight.
  have hYmin : ∀ (B : SecondSubconstituent G x) (side : Bool), IsE7Minimal (Y B side) := by
    intro B side
    have h := (e7e7Plus_norm_three_iff (M.generator B)).mp (M.generator_norm hG B)
    cases side
    · have hfun : Y B false =
          fun j => Matrix.vecMul (M.generator B) e7e7PlusCoords (Sum.inl j) := by
        funext j
        rw [hY]
        rfl
      rw [hfun]
      exact h.1
    · have hfun : Y B true =
          fun j => Matrix.vecMul (M.generator B) e7e7PlusCoords (Sum.inr j) := by
        funext j
        rw [hY]
        rfl
      rw [hfun]
      exact h.2
  have hYsq : ∀ (B : SecondSubconstituent G x) (side : Bool), ∑ i, (Y B side i) ^ 2 = 24 :=
    fun B side => (hYmin B side).sum_sq (by decide)
  -- the block sums vanish
  have hDsum : ∀ side, ∑ i, D side i = 0 := by
    intro side
    rw [Finset.sum_congr rfl fun i _ => hD side i]
    exact e7e7PlusBlock_sum side M.centroid
  -- glue parity: the centroid lies in `E₇ ⊕ E₇`
  have hcnorm : Matrix.toBilin' e7e7PlusGram M.centroid M.centroid = 2 * 150 := by
    have h := M.centroid_norm hG hc
    linarith
  have hres : ∀ side, ∃ r : ℤ, (2 : ℤ) ∣ r ∧ ∀ i, (4 : ℤ) ∣ (D side i - r) := by
    intro side
    obtain ⟨r, hr2, hr4⟩ := e7e7Plus_even_block_of_even_norm M.centroid hcnorm side
    exact ⟨r, hr2, fun i => by rw [hD]; exact hr4 i⟩
  exact ⟨{
    Y := Y
    D := D
    Y_eq := hY
    D_eq := hD
    D_five := hDfive
    subconstituent_card := hcard
    Y_minimal := hYmin
    Y_sq := hYsq
    D_sum := hDsum
    D_residue := hres }⟩

end Lattice
end SRG266
