/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusMatrixChecks
import SRG266.Lattice.Hosts.Model

/-! # Coordinate geometry of the glued E7 core -/

namespace SRG266
namespace Lattice

open scoped BigOperators Matrix

theorem e7e7PlusCoords_row_left_sum :
    ∀ i : Fin 14, ∑ j, e7e7PlusCoords i (Sum.inl j) = 0 := by
  decide +kernel

theorem e7e7PlusCoords_row_right_sum :
    ∀ i : Fin 14, ∑ j, e7e7PlusCoords i (Sum.inr j) = 0 := by
  decide +kernel

theorem e7e7PlusCoords_row_left_congruent :
    ∀ (i : Fin 14) (j : Fin 8),
      e7e7PlusCoords i (Sum.inl j) % 4 = e7e7PlusCoords i (Sum.inl 0) % 4 := by
  decide +kernel

theorem e7e7PlusCoords_row_right_congruent :
    ∀ (i : Fin 14) (j : Fin 8),
      e7e7PlusCoords i (Sum.inr j) % 4 = e7e7PlusCoords i (Sum.inr 0) % 4 := by
  decide +kernel

theorem e7e7PlusCoords_row_glue :
    ∀ i : Fin 14,
      (e7e7PlusCoords i (Sum.inl 0) - e7e7PlusCoords i (Sum.inr 0)) % 2 = 0 := by
  decide +kernel

theorem e7e7PlusCoords_row_mem (i : Fin 14) :
    (fun j => e7e7PlusCoords i j) ∈ gluedPairSubmodule (Fin 8) (Fin 8) := by
  refine ⟨e7e7PlusCoords_row_left_sum i, e7e7PlusCoords_row_right_sum i,
    e7e7PlusCoords i (Sum.inl 0), e7e7PlusCoords i (Sum.inr 0), fun j => ?_, fun j => ?_, ?_⟩
  · show (4 : ℤ) ∣ (e7e7PlusCoords i (Sum.inl j) - e7e7PlusCoords i (Sum.inl 0))
    have h := e7e7PlusCoords_row_left_congruent i j
    omega
  · show (4 : ℤ) ∣ (e7e7PlusCoords i (Sum.inr j) - e7e7PlusCoords i (Sum.inr 0))
    have h := e7e7PlusCoords_row_right_congruent i j
    omega
  · have h := e7e7PlusCoords_row_glue i
    omega

/-- **The coordinate presentation of `(E₇ ⊕ E₇)⁺`.** -/
theorem e7e7Plus_vecMul_mem (v : Fin 14 → ℤ) :
    Matrix.vecMul v e7e7PlusCoords ∈ gluedPairSubmodule (Fin 8) (Fin 8) :=
  vecMul_mem_submodule e7e7PlusCoords (gluedPairSubmodule (Fin 8) (Fin 8))
    e7e7PlusCoords_row_mem v

theorem e7e7Plus_block_split (v : Fin 14 → ℤ) :
    ∑ j, (Matrix.vecMul v e7e7PlusCoords j) ^ 2 =
      (∑ j, (Matrix.vecMul v e7e7PlusCoords (Sum.inl j)) ^ 2) +
        ∑ j, (Matrix.vecMul v e7e7PlusCoords (Sum.inr j)) ^ 2 :=
  Fintype.sum_sum_type _

/-- A vector of `(E₇ ⊕ E₇)⁺` has norm three exactly when both `E₇` components
are minimal vectors of
`E₇* ∖ E₇`, that is minuscule weights: `56 ^ 2 = 3136` vectors. -/
theorem e7e7Plus_norm_three_iff (v : Fin 14 → ℤ) :
    Matrix.toBilin' e7e7PlusGram v v = 3 ↔
      IsE7Minimal (fun j => Matrix.vecMul v e7e7PlusCoords (Sum.inl j)) ∧
        IsE7Minimal (fun j => Matrix.vecMul v e7e7PlusCoords (Sum.inr j)) := by
  rw [norm_three_iff_sum_sq e7e7PlusGram e7e7PlusCoords 4 (by norm_num)
    e7e7PlusCoords_gram v, e7e7Plus_block_split v]
  constructor
  · intro htotal
    exact gluedPair_norm_three (by decide) (by decide) (e7e7Plus_vecMul_mem v) (by omega)
  · rintro ⟨hleft, hright⟩
    rw [hleft.sum_sq (by decide), hright.sum_sq (by decide)]
    norm_num

/-! ## Blocks of a core vector -/

/-- One of the two `E₇` blocks of the scaled coordinates of a core vector. -/
def e7e7PlusBlock (side : Bool) (v : Fin 14 → ℤ) (i : Fin 8) : ℤ :=
  Matrix.vecMul v e7e7PlusCoords (if side then Sum.inr i else Sum.inl i)

theorem e7e7PlusBlock_sum (side : Bool) (v : Fin 14 → ℤ) :
    ∑ i, e7e7PlusBlock side v i = 0 := by
  have hmem := e7e7Plus_vecMul_mem v
  cases side
  · exact hmem.1
  · exact hmem.2.1

/-- The two blocks carry the whole pairing, scaled by `16`. -/
theorem e7e7PlusBlock_dot (v w : Fin 14 → ℤ) :
    (∑ i, e7e7PlusBlock false v i * e7e7PlusBlock false w i) +
        ∑ i, e7e7PlusBlock true v i * e7e7PlusBlock true w i =
      4 ^ 2 * Matrix.toBilin' e7e7PlusGram v w := by
  rw [← dotProduct_vecMul_coords e7e7PlusGram e7e7PlusCoords 4 e7e7PlusCoords_gram v w,
    dotProduct]
  exact (Fintype.sum_sum_type (α₁ := Fin 8) (α₂ := Fin 8)
    fun j => Matrix.vecMul v e7e7PlusCoords j * Matrix.vecMul w e7e7PlusCoords j).symm

/-- The two blocks carry the whole norm, scaled by `16`. -/
theorem e7e7PlusBlock_sum_sq (v : Fin 14 → ℤ) :
    (∑ i, (e7e7PlusBlock false v i) ^ 2) + ∑ i, (e7e7PlusBlock true v i) ^ 2 =
      4 ^ 2 * Matrix.toBilin' e7e7PlusGram v v := by
  rw [← e7e7PlusBlock_dot v v]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => sq (e7e7PlusBlock false v i)
  · exact Finset.sum_congr rfl fun i _ => sq (e7e7PlusBlock true v i)

/-- A core vector of even
norm lies in `E₇ ⊕ E₇`: both of its glue residues are even.  Otherwise both
blocks would have square sum congruent to `24` modulo `32`, and the total would
be congruent to `16` rather than `0`. -/
theorem e7e7Plus_even_block_of_even_norm (v : Fin 14 → ℤ) {m : ℤ}
    (hnorm : Matrix.toBilin' e7e7PlusGram v v = 2 * m) (side : Bool) :
    ∃ r : ℤ, (2 : ℤ) ∣ r ∧ ∀ i, (4 : ℤ) ∣ (e7e7PlusBlock side v i - r) := by
  have hmem := e7e7Plus_vecMul_mem v
  obtain ⟨r, s, hr, hs, hrl, hrr, hrs⟩ := gluedPair_residues_normalised hmem
  have hcard : Fintype.card (Fin 8) = 8 := by decide
  have hsq := e7e7PlusBlock_sum_sq v
  rw [hnorm] at hsq
  have heven : (2 : ℤ) ∣ r := by
    by_contra hodd
    have hrodd : r = 1 ∨ r = 3 := by omega
    have hsodd : s = 1 ∨ s = 3 := by
      obtain ⟨k, hk⟩ := hrs
      omega
    obtain ⟨kl, hkl⟩ := sumZeroCongruent_odd_mod_thirtyTwo hcard hrodd
      (e7e7PlusBlock_sum false v) hrl
    obtain ⟨kr, hkr⟩ := sumZeroCongruent_odd_mod_thirtyTwo hcard hsodd
      (e7e7PlusBlock_sum true v) hrr
    omega
  have hevens : (2 : ℤ) ∣ s := by
    obtain ⟨k, hk⟩ := hrs
    obtain ⟨l, hl⟩ := heven
    exact ⟨l - k, by omega⟩
  cases side
  · exact ⟨r, heven, hrl⟩
  · exact ⟨s, hevens, hrr⟩

end Lattice
end SRG266
