/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Hosts.E7E7PlusZRowChecks
import SRG266.Lattice.Hosts.E7E7PlusZMatrixChecks

/-! # Coordinate geometry of the rank-15 E7 host -/

namespace SRG266
namespace Lattice

open scoped BigOperators Matrix

theorem e7e7PlusZUnit_mem (v : Fin 15 → ℤ) :
    ∀ j, (4 : ℤ) ∣ Matrix.vecMul v (fun i j => e7e7PlusZCoords i (Sum.inl j)) j := by
  refine vecMul_mem_submodule (fun i j => e7e7PlusZCoords i (Sum.inl j))
    (scaleSubmodule 4 (Fin 1)) (fun i => ?_) v
  intro j
  show (4 : ℤ) ∣ e7e7PlusZCoords i (Sum.inl j)
  have h := e7e7PlusZCoords_row_unit i j
  omega

theorem e7e7PlusZPair_mem (v : Fin 15 → ℤ) :
    Matrix.vecMul v e7e7PlusZPair ∈ gluedPairSubmodule (Fin 8) (Fin 8) := by
  refine vecMul_mem_submodule e7e7PlusZPair (gluedPairSubmodule (Fin 8) (Fin 8))
    (fun i => ?_) v
  refine ⟨e7e7PlusZPair_row_left_sum i, e7e7PlusZPair_row_right_sum i,
    e7e7PlusZPair i (Sum.inl 0), e7e7PlusZPair i (Sum.inr 0), fun j => ?_, fun j => ?_, ?_⟩
  · show (4 : ℤ) ∣ (e7e7PlusZPair i (Sum.inl j) - e7e7PlusZPair i (Sum.inl 0))
    have h := e7e7PlusZPair_row_left_congruent i j
    omega
  · show (4 : ℤ) ∣ (e7e7PlusZPair i (Sum.inr j) - e7e7PlusZPair i (Sum.inr 0))
    have h := e7e7PlusZPair_row_right_congruent i j
    omega
  · have h := e7e7PlusZPair_row_glue i
    omega

theorem e7e7PlusZ_block_split (v : Fin 15 → ℤ) :
    ∑ j, (Matrix.vecMul v e7e7PlusZCoords j) ^ 2 =
      (Matrix.vecMul v e7e7PlusZCoords (Sum.inl 0)) ^ 2 +
        ((∑ j, (Matrix.vecMul v e7e7PlusZPair (Sum.inl j)) ^ 2) +
          ∑ j, (Matrix.vecMul v e7e7PlusZPair (Sum.inr j)) ^ 2) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · rw [Finset.sum_congr rfl fun j _ =>
      show (Matrix.vecMul v e7e7PlusZCoords (Sum.inl j)) ^ 2 =
        (Matrix.vecMul v e7e7PlusZCoords (Sum.inl 0)) ^ 2 by
      rcases j with ⟨j, hj⟩
      interval_cases j
      rfl]
    simp

/-- The block form of the norm-three condition for the host: the `ℤ` block, the
first `E₇` block and the second `E₇` block, with square sums adding to `48`. -/
theorem e7e7PlusZ_blocks_iff (c : ℤ) (y : E7E7PlusIndex → ℤ) (hc : (4 : ℤ) ∣ c)
    (hy : y ∈ gluedPairSubmodule (Fin 8) (Fin 8)) :
    c ^ 2 + ((∑ j, (y (Sum.inl j)) ^ 2) + ∑ j, (y (Sum.inr j)) ^ 2) = 48 ↔
      ((c = 0) ∧ IsE7Minimal (fun j => y (Sum.inl j)) ∧
          IsE7Minimal (fun j => y (Sum.inr j))) ∨
        ((c = 4 ∨ c = -4) ∧
          (((∀ j, y (Sum.inl j) = 0) ∧ ∑ j, (y (Sum.inr j)) ^ 2 = 32) ∨
            ((∀ j, y (Sum.inr j) = 0) ∧ ∑ j, (y (Sum.inl j)) ^ 2 = 32))) := by
  have hnnl : (0 : ℤ) ≤ ∑ j, (y (Sum.inl j)) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg (y (Sum.inl j))
  have hnnr : (0 : ℤ) ≤ ∑ j, (y (Sum.inr j)) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg (y (Sum.inr j))
  obtain ⟨k, hk⟩ := hc
  have hsuml : ∑ j, y (Sum.inl j) = 0 := hy.1
  have hsumr : ∑ j, y (Sum.inr j) = 0 := hy.2.1
  obtain ⟨r, s, hr, hs, hrl, hrr, hrs⟩ := gluedPair_residues_normalised hy
  have hcard : Fintype.card (Fin 8) = 4 * 2 := by decide
  constructor
  · intro htotal
    have hcsq : (0 : ℤ) ≤ c ^ 2 := sq_nonneg c
    by_cases hre : r = 0 ∨ r = 2
    · -- both glue residues even: each `E₇` block has square sum divisible by `32`
      have hse : s = 0 ∨ s = 2 := by
        obtain ⟨t, ht⟩ := hrs
        omega
      obtain ⟨kl, hkl⟩ := sumZeroCongruent_even_dvd (m := 2) hcard (by norm_num)
        (r := r) (by omega) hsuml hrl
      obtain ⟨kr, hkr⟩ := sumZeroCongruent_even_dvd (m := 2) hcard (by norm_num)
        (r := s) (by omega) hsumr hrr
      have hcbound : c ^ 2 ≤ 48 := by omega
      have hlow : -6 ≤ c := by nlinarith
      have hhigh : c ≤ 6 := by nlinarith
      have hcval : c = -4 ∨ c = 0 ∨ c = 4 := by omega
      have hczero : c = 4 ∨ c = -4 := by
        rcases hcval with h | h | h
        · exact Or.inr h
        · exfalso
          have : c ^ 2 = 0 := by rw [h]; norm_num
          omega
        · exact Or.inl h
      refine Or.inr ⟨hczero, ?_⟩
      have hc16 : c ^ 2 = 16 := by
        rcases hczero with h | h <;> rw [h] <;> norm_num
      have hsplit : kl = 0 ∨ kr = 0 := by omega
      rcases hsplit with hkl0 | hkr0
      · have hlzero : ∑ j, (y (Sum.inl j)) ^ 2 = 0 := by omega
        exact Or.inl ⟨fun j => eq_zero_of_sum_sq_eq_zero (fun j => y (Sum.inl j)) hlzero j,
          by omega⟩
      · have hrzero : ∑ j, (y (Sum.inr j)) ^ 2 = 0 := by omega
        exact Or.inr ⟨fun j => eq_zero_of_sum_sq_eq_zero (fun j => y (Sum.inr j)) hrzero j,
          by omega⟩
    · -- both glue residues odd: both blocks are at least minimal
      have hrodd : r = 1 ∨ r = 3 := by omega
      have hsodd : s = 1 ∨ s = 3 := by
        obtain ⟨t, ht⟩ := hrs
        omega
      have hboundl := sumZeroCongruent_odd_bound (m := 2) hcard hrodd hsuml hrl
      have hboundr := sumZeroCongruent_odd_bound (m := 2) hcard hsodd hsumr hrr
      push_cast at hboundl hboundr
      have hc2 : c ^ 2 = 0 := by omega
      have hczero : c = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc2
      refine Or.inl ⟨hczero, ?_, ?_⟩
      · exact sumZeroCongruent_odd_shell (m := 2) hcard hrodd hsuml hrl (by push_cast; omega)
      · exact sumZeroCongruent_odd_shell (m := 2) hcard hsodd hsumr hrr (by push_cast; omega)
  · intro hcases
    rcases hcases with ⟨hczero, hminl, hminr⟩ | ⟨hcval, hblocks⟩
    · rw [hczero, hminl.sum_sq (by decide), hminr.sum_sq (by decide)]
      norm_num
    · have hcc : c ^ 2 = 16 := by rcases hcval with h | h <;> rw [h] <;> norm_num
      rcases hblocks with ⟨hzero, hroot⟩ | ⟨hzero, hroot⟩
      · have : ∑ j, (y (Sum.inl j)) ^ 2 = 0 :=
          Finset.sum_eq_zero fun j _ => by rw [hzero j]; norm_num
        omega
      · have : ∑ j, (y (Sum.inr j)) ^ 2 = 0 :=
          Finset.sum_eq_zero fun j _ => by rw [hzero j]; norm_num
        omega

/-- A norm-three vector of `(E₇ ⊕ E₇)⁺ ⊕ ℤ` is either a pair of minuscule
weights with vanishing `ℤ` coordinate, or the
sum of a root of one `E₇` factor and a unit vector of `ℤ`:
`3136 + 504 = 3640` vectors. -/
theorem e7e7PlusZ_norm_three_iff (v : Fin 15 → ℤ) :
    Matrix.toBilin' e7e7PlusZGram v v = 3 ↔
      ((Matrix.vecMul v e7e7PlusZCoords (Sum.inl 0) = 0) ∧
          IsE7Minimal (fun j => Matrix.vecMul v e7e7PlusZPair (Sum.inl j)) ∧
          IsE7Minimal (fun j => Matrix.vecMul v e7e7PlusZPair (Sum.inr j))) ∨
        ((Matrix.vecMul v e7e7PlusZCoords (Sum.inl 0) = 4 ∨
            Matrix.vecMul v e7e7PlusZCoords (Sum.inl 0) = -4) ∧
          (((∀ j, Matrix.vecMul v e7e7PlusZPair (Sum.inl j) = 0) ∧
              ∑ j, (Matrix.vecMul v e7e7PlusZPair (Sum.inr j)) ^ 2 = 32) ∨
            ((∀ j, Matrix.vecMul v e7e7PlusZPair (Sum.inr j) = 0) ∧
              ∑ j, (Matrix.vecMul v e7e7PlusZPair (Sum.inl j)) ^ 2 = 32))) := by
  rw [norm_three_iff_sum_sq e7e7PlusZGram e7e7PlusZCoords 4 (by norm_num)
    e7e7PlusZCoords_gram v, e7e7PlusZ_block_split v, show (3 : ℤ) * 4 ^ 2 = 48 by norm_num]
  exact e7e7PlusZ_blocks_iff _ _ (e7e7PlusZUnit_mem v 0) (e7e7PlusZPair_mem v)

end Lattice
end SRG266
