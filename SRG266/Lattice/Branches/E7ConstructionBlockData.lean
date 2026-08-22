/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Branches.E7RawConstructionData

/-!
# Arithmetic block data for the E7 branch

This module extracts the two E7 coordinate blocks, their parity reductions,
and the complementary component norms from a pure `(E₇ ⊕ E₇)⁺` core model.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

set_option maxRecDepth 40000

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {G}

/-- The arithmetic data available before canonical coordinate sorting. -/
structure E7ConstructionBlockData {x : V}
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (M : PureCoreModel E c e7e7PlusGram) where
  Y : SecondSubconstituent G x → Bool → Fin 8 → ℤ
  D : Bool → Fin 8 → ℤ
  par : Bool → ℕ
  a : Bool → Fin 8 → ℤ
  n : Bool → ℤ
  Y_eq : ∀ B side i, Y B side i = e7e7PlusBlock side (M.generator B) i
  D_eq : ∀ side i, D side i = e7e7PlusBlock side M.centroid i
  D_five : ∀ side i, (5 : ℤ) ∣ D side i
  subconstituent_card :
    (Finset.univ : Finset (SecondSubconstituent G x)).card = 220
  Y_minimal : ∀ B side, IsE7Minimal (Y B side)
  Y_sq : ∀ B side, ∑ i, (Y B side i) ^ 2 = 24
  D_sum : ∀ side, ∑ i, D side i = 0
  par_cases : ∀ side, par side = 0 ∨ par side = 1
  D_split : ∀ side i, D side i = 2 * (2 * a side i + (par side : ℤ))
  D_sq : ∀ side, ∑ i, (D side i) ^ 2 = 16 * n side
  n_even : ∀ side, (2 : ℤ) ∣ n side
  n_total : n false + n true = 300
  n_le_threeHundred : ∀ side, n side ≤ 300

/-- Extract the arithmetic block data before canonical sorting. -/
theorem e7ConstructionBlockData_of_pureCoreModel {x : V}
    (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c e7e7PlusGram) :
    Nonempty (E7ConstructionBlockData M) := by
  classical
  obtain ⟨R⟩ := e7RawConstructionData_of_pureCoreModel hG hc M
  rcases R with ⟨Y, D, hY, hD, hDfive, hcard, hYmin, hYsq, hDsum, hres⟩
  -- reduced coordinates of each factor
  have hsplit : ∀ side, ∃ (par : ℕ) (a : Fin 8 → ℤ), (par = 0 ∨ par = 1) ∧
      ∀ i, D side i = 2 * (2 * a i + (par : ℤ)) := by
    intro side
    obtain ⟨r, hr2, hr4⟩ := hres side
    obtain ⟨q, hq⟩ := hr2
    choose k hk using hr4
    refine ⟨(q % 2).toNat, fun i => (q - q % 2) / 2 + k i, by omega, fun i => ?_⟩
    show D side i = 2 * (2 * ((q - q % 2) / 2 + k i) + ((q % 2).toNat : ℤ))
    have hki := hk i
    omega
  choose par a hpar01 hDa using hsplit
  -- the two component norms
  have hDsq : ∀ side, ∃ n : ℤ, ∑ i, (D side i) ^ 2 = 16 * n ∧ (2 : ℤ) ∣ n := by
    intro side
    obtain ⟨r, hr2, hr4⟩ := hres side
    obtain ⟨u, hu⟩ := sumZeroCongruent_even_dvd (m := 2) (by decide) (by norm_num)
      (r := r) hr2 (hDsum side) hr4
    exact ⟨2 * u, by omega, ⟨u, rfl⟩⟩
  choose n hn hneven using hDsq
  have htotal : n false + n true = 300 := by
    have h := e7e7PlusBlock_sum_sq M.centroid
    rw [M.centroid_norm hG hc] at h
    have hleft : ∑ i, (e7e7PlusBlock false M.centroid i) ^ 2 = ∑ i, (D false i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hD false i]
    have hright : ∑ i, (e7e7PlusBlock true M.centroid i) ^ 2 = ∑ i, (D true i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hD true i]
    rw [hleft, hright, hn false, hn true] at h
    omega
  have hnnonneg : ∀ side, 0 ≤ n side := by
    intro side
    have h : (0 : ℤ) ≤ ∑ i, (D side i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [hn side] at h
    omega
  -- the reduced invariants
  have hn300 : ∀ side, n side ≤ 300 := by
    intro side
    have h0 := hnnonneg false
    have h1 := hnnonneg true
    cases side <;> omega
  exact ⟨{
    Y := Y
    D := D
    par := par
    a := a
    n := n
    Y_eq := hY
    D_eq := hD
    D_five := hDfive
    subconstituent_card := hcard
    Y_minimal := hYmin
    Y_sq := hYsq
    D_sum := hDsum
    par_cases := hpar01
    D_split := hDa
    D_sq := hn
    n_even := hneven
    n_total := htotal
    n_le_threeHundred := hn300 }⟩

end Lattice
end SRG266
