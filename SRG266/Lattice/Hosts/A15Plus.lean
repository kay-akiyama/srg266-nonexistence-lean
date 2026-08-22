/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.Rank15HostGramData
import SRG266.Lattice.HostCertificate
import SRG266.Lattice.Hosts.Model

/-!
# The host `A₁₅⁺`

The rank-15 host `A₁₅⁺ = A₁₅ + ℤ[4]` lies inside the sum-zero hyperplane
of `ℝ¹⁶` and is presented with
scale `4`, so that `4 • A₁₅⁺` is exactly the sum-zero mod-4 model
`SRG266.Lattice.SumZeroCongruent` on sixteen coordinates.

* `SRG266.Lattice.a15PlusHost : SRG266.OddUnimodularLattice15`;
* `SRG266.Lattice.a15Plus_norm_three_iff` — the `3640` norm-three vectors are
  exactly the `-3`-on-a-four-set patterns and their negatives;
* `SRG266.Lattice.a15Plus_residue_of_even_norm` — a vector of even norm, such as
  the centroid of norm `300`, has even glue residue (the side
  condition `residue ∈ {0, 2}` of `SRG266.AuditedRank15HostCase.a15Plus`).
-/

namespace SRG266
namespace Lattice

open Finset

set_option maxRecDepth 8000

/-! ## The generated data, as matrices -/

/-- Gram matrix of the generated basis of `A₁₅⁺`. -/
def a15PlusGram : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => (a15PlusGramData.getD i.1 #[]).getD j.1 0

/-- Inverse of `a15PlusGram`. -/
def a15PlusGramInv : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => (a15PlusGramInvData.getD i.1 #[]).getD j.1 0

/-- Lower factor of the LDLᵀ certificate of `a15PlusGram`. -/
def a15PlusLdltFactor : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => (a15PlusLdltFactorData.getD i.1 #[]).getD j.1 0

/-- Weights of the LDLᵀ certificate of `a15PlusGram`. -/
def a15PlusLdltWeight : Fin 15 → ℤ :=
  fun k => a15PlusLdltWeightData.getD k.1 0

/-- Basis of `A₁₅⁺` in model coordinates, scaled by `4`. -/
def a15PlusCoords : Matrix (Fin 15) (Fin 16) ℤ :=
  fun i j => (a15PlusCoordsData.getD i.1 #[]).getD j.1 0

/-! ## Kernel checks -/

theorem a15PlusGram_entries_symm : ∀ i j, a15PlusGram i j = a15PlusGram j i := by
  decide +kernel

theorem a15PlusGram_isSymm : a15PlusGram.IsSymm :=
  isSymm_of_entries a15PlusGram a15PlusGram_entries_symm

theorem a15PlusGram_mul_inv : a15PlusGram * a15PlusGramInv = 1 :=
  mul_eq_one_of_entries a15PlusGram a15PlusGramInv (by decide +kernel)

theorem a15PlusGram_ldlt :
    checkIntegerScaledGram a15PlusGram a15PlusLdltFactor a15PlusLdltWeight
      a15PlusLdltScale = true := by
  decide +kernel

theorem a15PlusCoords_gram :
    ∀ i j, (a15PlusCoords * a15PlusCoords.transpose) i j = 4 ^ 2 * a15PlusGram i j := by
  decide +kernel

/-! ## The host -/

theorem a15PlusGram_posDef :
    ∀ v : Fin 15 → ℤ, v ≠ 0 → 0 < Matrix.toBilin' a15PlusGram v v :=
  toBilin'_posDef_of_ldlt a15PlusGram a15PlusGramInv a15PlusLdltFactor a15PlusLdltWeight
    a15PlusLdltScale a15PlusGram_isSymm a15PlusGram_mul_inv a15PlusGram_ldlt

/-- **The host `A₁₅⁺`.** -/
noncomputable def a15PlusHost : OddUnimodularLattice15 :=
  hostOfMatrix a15PlusGram a15PlusGramInv a15PlusGram_isSymm a15PlusGram_mul_inv
    a15PlusGram_posDef (by decide +kernel)

/-! ## The coordinate model -/

theorem a15PlusCoords_row_sum : ∀ i : Fin 15, ∑ j, a15PlusCoords i j = 0 := by
  decide +kernel

theorem a15PlusCoords_row_congruent :
    ∀ (i : Fin 15) (j : Fin 16), a15PlusCoords i j % 4 = a15PlusCoords i 0 % 4 := by
  decide +kernel

theorem a15PlusCoords_row_mem (i : Fin 15) :
    (fun j => a15PlusCoords i j) ∈ sumZeroCongruentSubmodule (Fin 16) := by
  refine ⟨a15PlusCoords_row_sum i, a15PlusCoords i 0, fun j => ?_⟩
  show (4 : ℤ) ∣ (a15PlusCoords i j - a15PlusCoords i 0)
  have h := a15PlusCoords_row_congruent i j
  omega

/-- **The coordinate presentation of `A₁₅⁺`.**  Every lattice vector maps to a
sum-zero vector of `ℤ¹⁶` whose entries share a residue modulo `4`. -/
theorem a15Plus_vecMul_mem (v : Fin 15 → ℤ) :
    SumZeroCongruent (Matrix.vecMul v a15PlusCoords) :=
  vecMul_mem_submodule a15PlusCoords (sumZeroCongruentSubmodule (Fin 16))
    a15PlusCoords_row_mem v

theorem a15Plus_coords_injective :
    Function.Injective fun v : Fin 15 → ℤ => Matrix.vecMul v a15PlusCoords :=
  vecMul_coords_injective a15PlusGram a15PlusGramInv a15PlusCoords 4 (by norm_num)
    a15PlusGram_mul_inv a15PlusCoords_gram

/-! ## The norm-three shell -/

private theorem a15Plus_card : Fintype.card (Fin 16) = 4 * 4 := by decide

/-- A lattice vector in `A₁₅⁺` has norm three
exactly when its scaled coordinates are `-3` on a four-element subset and `1`
elsewhere, or the negative of such a vector.  There are
`2 * Nat.choose 16 4 = 3640` of them. -/
theorem a15Plus_norm_three_iff (v : Fin 15 → ℤ) :
    Matrix.toBilin' a15PlusGram v v = 3 ↔
      ∃ S : Finset (Fin 16), S.card = 4 ∧
        ((∀ j, Matrix.vecMul v a15PlusCoords j = if j ∈ S then -3 else 1) ∨
          (∀ j, Matrix.vecMul v a15PlusCoords j = if j ∈ S then 3 else -1)) := by
  rw [norm_three_iff_sum_sq a15PlusGram a15PlusCoords 4 (by norm_num) a15PlusCoords_gram v]
  obtain ⟨hsum, -⟩ := a15Plus_vecMul_mem v
  obtain ⟨r, hr, hcong⟩ := (a15Plus_vecMul_mem v).residue_normalised
  set y := Matrix.vecMul v a15PlusCoords with hy
  constructor
  · intro hnorm
    have hnorm' : ∑ j, (y j) ^ 2 = 16 * 3 := by
      rw [hnorm]
      ring
    have hpar := sumZeroCongruent_norm_residue_parity a15Plus_card hsum hcong 3 hnorm'
    have hodd : r = 1 ∨ r = 3 := by omega
    have hshell := sumZeroCongruent_odd_shell (m := 4) a15Plus_card hodd hsum hcong
      (by rw [hnorm']; norm_num)
    obtain ⟨S, hcard, hcases⟩ := hshell
    exact ⟨S, hcard, hcases⟩
  · rintro ⟨S, hcard, hpattern⟩
    have hvalue : ∀ j, (y j) ^ 2 = if j ∈ S then (9 : ℤ) else 1 := by
      intro j
      rcases hpattern with hp | hp <;> rw [hp j] <;> by_cases hj : j ∈ S <;>
        simp [hj]
    calc ∑ j, (y j) ^ 2 = ∑ j, (if j ∈ S then (9 : ℤ) else 1) :=
          Finset.sum_congr rfl fun j _ => hvalue j
      _ = 3 * 4 ^ 2 := by
          rw [sum_ite_mem_const S 9 1, hcard]
          norm_num

/-- The centroid of the
embedded generators has norm `300`, so its glue residue is `0` or `2` — the
side condition `residue_cases` of `SRG266.AuditedRank15HostCase.a15Plus`. -/
theorem a15Plus_residue_of_even_norm (v : Fin 15 → ℤ) (N : ℤ) (hN : (2 : ℤ) ∣ N)
    (hnorm : Matrix.toBilin' a15PlusGram v v = N) {r : ℤ}
    (hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3)
    (hcong : ∀ j, (4 : ℤ) ∣ (Matrix.vecMul v a15PlusCoords j - r)) :
    r = 0 ∨ r = 2 := by
  obtain ⟨hsum, -⟩ := a15Plus_vecMul_mem v
  have hnorm' : ∑ j, (Matrix.vecMul v a15PlusCoords j) ^ 2 = 16 * N := by
    rw [sum_sq_vecMul_coords a15PlusGram a15PlusCoords 4 a15PlusCoords_gram v, hnorm]
    ring
  have hpar := sumZeroCongruent_norm_residue_parity a15Plus_card hsum hcong N hnorm'
  obtain ⟨k, hk⟩ := hN
  omega

end Lattice
end SRG266
