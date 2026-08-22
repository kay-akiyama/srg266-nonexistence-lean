/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.Rank15HostGramData
import SRG266.Lattice.HostCertificate
import SRG266.Lattice.Hosts.Model

/-!
# The core `E₈` and the host `E₈ ⊕ ℤ⁷`

Both lattices are presented with scale `2`: `2 • E₈` is the same-parity model
`SRG266.Lattice.SameParitySumFour` on eight coordinates, and the host adds a
`ℤ⁷` block whose scaled coordinates are the even integers.

* `SRG266.Lattice.e8_norm_even` — `E₈` is an even lattice, so it has no
  norm-three vector;
* `SRG266.Lattice.e8z7Host : SRG266.OddUnimodularLattice15`;
* `SRG266.Lattice.e8z7_norm_three_iff` — the `3640` norm-three vectors of the
  host are the `3360` sums of an `E₈` root and a unit vector of `ℤ⁷`, and the
  `280` vectors with three coordinates `±1` inside `ℤ⁷`.
-/

namespace SRG266
namespace Lattice

open Finset

set_option maxRecDepth 8000

/-! ## The core `E₈` -/

/-- Gram matrix of the generated basis of `E₈`. -/
def e8Gram : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => (e8GramData.getD i.1 #[]).getD j.1 0

/-- Inverse of `e8Gram`. -/
def e8GramInv : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => (e8GramInvData.getD i.1 #[]).getD j.1 0

/-- Lower factor of the LDLᵀ certificate of `e8Gram`. -/
def e8LdltFactor : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => (e8LdltFactorData.getD i.1 #[]).getD j.1 0

/-- Weights of the LDLᵀ certificate of `e8Gram`. -/
def e8LdltWeight : Fin 8 → ℤ :=
  fun k => e8LdltWeightData.getD k.1 0

/-- Basis of `E₈` in model coordinates, scaled by `2`. -/
def e8Coords : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => (e8CoordsData.getD i.1 #[]).getD j.1 0

theorem e8Gram_entries_symm : ∀ i j, e8Gram i j = e8Gram j i := by
  decide +kernel

theorem e8Gram_isSymm : e8Gram.IsSymm :=
  isSymm_of_entries e8Gram e8Gram_entries_symm

theorem e8Gram_mul_inv : e8Gram * e8GramInv = 1 :=
  mul_eq_one_of_entries e8Gram e8GramInv (by decide +kernel)

theorem e8Gram_ldlt :
    checkIntegerScaledGram e8Gram e8LdltFactor e8LdltWeight e8LdltScale = true := by
  decide +kernel

theorem e8Coords_gram :
    ∀ i j, (e8Coords * e8Coords.transpose) i j = 2 ^ 2 * e8Gram i j := by
  decide +kernel

theorem e8Gram_posDef : ∀ v : Fin 8 → ℤ, v ≠ 0 → 0 < Matrix.toBilin' e8Gram v v :=
  toBilin'_posDef_of_ldlt e8Gram e8GramInv e8LdltFactor e8LdltWeight e8LdltScale
    e8Gram_isSymm e8Gram_mul_inv e8Gram_ldlt

theorem e8Coords_row_parity :
    ∀ (i : Fin 8) (j : Fin 8), e8Coords i j % 2 = e8Coords i 0 % 2 := by
  decide +kernel

theorem e8Coords_row_sum : ∀ i : Fin 8, (∑ j, e8Coords i j) % 4 = 0 := by
  decide +kernel

theorem e8Coords_row_mem (i : Fin 8) :
    (fun j => e8Coords i j) ∈ sameParitySubmodule (Fin 8) := by
  refine ⟨⟨e8Coords i 0, fun j => ?_⟩, ?_⟩
  · show (2 : ℤ) ∣ (e8Coords i j - e8Coords i 0)
    have h := e8Coords_row_parity i j
    omega
  · show (4 : ℤ) ∣ ∑ j, e8Coords i j
    have h := e8Coords_row_sum i
    omega

/-- **The coordinate presentation of `E₈`.** -/
theorem e8_vecMul_mem (v : Fin 8 → ℤ) : SameParitySumFour (Matrix.vecMul v e8Coords) :=
  vecMul_mem_submodule e8Coords (sameParitySubmodule (Fin 8)) e8Coords_row_mem v

/-- Every vector in `E₈` has even norm. -/
theorem e8_norm_even (v : Fin 8 → ℤ) : (2 : ℤ) ∣ Matrix.toBilin' e8Gram v v := by
  have hsum := sum_sq_vecMul_coords e8Gram e8Coords 2 e8Coords_gram v
  obtain ⟨k, hk⟩ := sameParity_dvd_eight (by decide) (e8_vecMul_mem v)
  exact ⟨k, by omega⟩

/-- `E₈` has no norm-three vector, so it cannot host a norm-three generator. -/
theorem e8_norm_ne_three (v : Fin 8 → ℤ) : Matrix.toBilin' e8Gram v v ≠ 3 := by
  intro h
  obtain ⟨k, hk⟩ := e8_norm_even v
  omega

/-! ## The host `E₈ ⊕ ℤ⁷` -/

/-- Index of the host model: seven `ℤ` coordinates and eight `E₈`
coordinates. -/
abbrev E8Z7Index := Fin 7 ⊕ Fin 8

/-- Linear position of a host coordinate in the generated data. -/
def e8z7Position : E8Z7Index → ℕ :=
  Sum.elim (fun k => k.1) (fun k => 7 + k.1)

/-- Gram matrix of the generated basis of `E₈ ⊕ ℤ⁷`. -/
def e8z7Gram : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => (e8z7GramData.getD i.1 #[]).getD j.1 0

/-- Inverse of `e8z7Gram`. -/
def e8z7GramInv : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => (e8z7GramInvData.getD i.1 #[]).getD j.1 0

/-- Lower factor of the LDLᵀ certificate of `e8z7Gram`. -/
def e8z7LdltFactor : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => (e8z7LdltFactorData.getD i.1 #[]).getD j.1 0

/-- Weights of the LDLᵀ certificate of `e8z7Gram`. -/
def e8z7LdltWeight : Fin 15 → ℤ :=
  fun k => e8z7LdltWeightData.getD k.1 0

/-- Basis of `E₈ ⊕ ℤ⁷` in model coordinates, scaled by `2`. -/
def e8z7Coords : Matrix (Fin 15) E8Z7Index ℤ :=
  fun i j => (e8z7CoordsData.getD i.1 #[]).getD (e8z7Position j) 0

/-- The `ℤ⁷` block of the coordinate matrix. -/
def e8z7Left : Matrix (Fin 15) (Fin 7) ℤ :=
  fun i j => e8z7Coords i (Sum.inl j)

/-- The `E₈` block of the coordinate matrix. -/
def e8z7Right : Matrix (Fin 15) (Fin 8) ℤ :=
  fun i j => e8z7Coords i (Sum.inr j)

theorem e8z7Gram_entries_symm : ∀ i j, e8z7Gram i j = e8z7Gram j i := by
  decide +kernel

theorem e8z7Gram_isSymm : e8z7Gram.IsSymm :=
  isSymm_of_entries e8z7Gram e8z7Gram_entries_symm

theorem e8z7Gram_mul_inv : e8z7Gram * e8z7GramInv = 1 :=
  mul_eq_one_of_entries e8z7Gram e8z7GramInv (by decide +kernel)

theorem e8z7Gram_ldlt :
    checkIntegerScaledGram e8z7Gram e8z7LdltFactor e8z7LdltWeight e8z7LdltScale = true := by
  decide +kernel

theorem e8z7Coords_gram :
    ∀ i j, (e8z7Coords * e8z7Coords.transpose) i j = 2 ^ 2 * e8z7Gram i j := by
  decide +kernel

theorem e8z7Gram_posDef : ∀ v : Fin 15 → ℤ, v ≠ 0 → 0 < Matrix.toBilin' e8z7Gram v v :=
  toBilin'_posDef_of_ldlt e8z7Gram e8z7GramInv e8z7LdltFactor e8z7LdltWeight e8z7LdltScale
    e8z7Gram_isSymm e8z7Gram_mul_inv e8z7Gram_ldlt

/-- **The host `E₈ ⊕ ℤ⁷`.** -/
noncomputable def e8z7Host : OddUnimodularLattice15 :=
  hostOfMatrix e8z7Gram e8z7GramInv e8z7Gram_isSymm e8z7Gram_mul_inv e8z7Gram_posDef
    (by decide +kernel)

/-! ## The coordinate model of the host -/

theorem e8z7Left_row_even : ∀ (i : Fin 15) (j : Fin 7), e8z7Left i j % 2 = 0 := by
  decide +kernel

theorem e8z7Right_row_parity :
    ∀ (i : Fin 15) (j : Fin 8), e8z7Right i j % 2 = e8z7Right i 0 % 2 := by
  decide +kernel

theorem e8z7Right_row_sum : ∀ i : Fin 15, (∑ j, e8z7Right i j) % 4 = 0 := by
  decide +kernel

theorem e8z7Left_mem (v : Fin 15 → ℤ) : ∀ j, (2 : ℤ) ∣ Matrix.vecMul v e8z7Left j := by
  refine vecMul_mem_submodule e8z7Left (scaleSubmodule 2 (Fin 7)) (fun i => ?_) v
  intro j
  show (2 : ℤ) ∣ e8z7Left i j
  have h := e8z7Left_row_even i j
  omega

theorem e8z7Right_mem (v : Fin 15 → ℤ) : SameParitySumFour (Matrix.vecMul v e8z7Right) := by
  refine vecMul_mem_submodule e8z7Right (sameParitySubmodule (Fin 8)) (fun i => ?_) v
  refine ⟨⟨e8z7Right i 0, fun j => ?_⟩, ?_⟩
  · show (2 : ℤ) ∣ (e8z7Right i j - e8z7Right i 0)
    have h := e8z7Right_row_parity i j
    omega
  · show (4 : ℤ) ∣ ∑ j, e8z7Right i j
    have h := e8z7Right_row_sum i
    omega

theorem e8z7_block_split (v : Fin 15 → ℤ) :
    ∑ j, (Matrix.vecMul v e8z7Coords j) ^ 2 =
      (∑ j, (Matrix.vecMul v e8z7Left j) ^ 2) + ∑ j, (Matrix.vecMul v e8z7Right j) ^ 2 := by
  rw [Fintype.sum_sum_type]
  rfl

/-- The block form of the norm-three condition: an even `ℤ⁷` block and an even
`E₈` block whose square sums add up to `12`. -/
theorem e8z7_blocks_iff (a : Fin 7 → ℤ) (b : Fin 8 → ℤ) (hleft : ∀ j, (2 : ℤ) ∣ a j)
    (hright : SameParitySumFour b) :
    (∑ j, (a j) ^ 2) + (∑ j, (b j) ^ 2) = 12 ↔
      ((∀ j, b j = 0) ∧ (∀ j, a j = 0 ∨ a j = 2 ∨ a j = -2) ∧
          (univ.filter fun j => a j ≠ 0).card = 3) ∨
        ((∑ j, (b j) ^ 2 = 8) ∧ (∀ j, a j = 0 ∨ a j = 2 ∨ a j = -2) ∧
          (univ.filter fun j => a j ≠ 0).card = 1) := by
  have hnn : (0 : ℤ) ≤ ∑ j, (a j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (a j)
  have hnn' : (0 : ℤ) ≤ ∑ j, (b j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (b j)
  constructor
  · intro htotal
    obtain ⟨k, hk⟩ := sameParity_dvd_eight (by decide) hright
    have hsigns : ∀ j, a j = 0 ∨ a j = 2 ∨ a j = -2 :=
      fun j => eq_zero_or_abs_scale_of_sum_sq_lt (c := 2) (by norm_num) a
        (∑ j, (a j) ^ 2) (by omega) hleft rfl j
    have hcount : ∑ j, (a j) ^ 2 = 4 * ((univ.filter fun j => a j ≠ 0).card : ℤ) := by
      rw [sum_sq_eq_sq_mul_card_support (c := 2) a hsigns]
      norm_num
    have hcardnn : (0 : ℤ) ≤ ((univ.filter fun j => a j ≠ 0).card : ℤ) :=
      Int.natCast_nonneg _
    have hk0 : k = 0 ∨ k = 1 := by omega
    rcases hk0 with hk0 | hk1
    · refine Or.inl ⟨fun j => eq_zero_of_sum_sq_eq_zero b (by omega) j, hsigns, ?_⟩
      have hc : ((univ.filter fun j => a j ≠ 0).card : ℤ) = 3 := by omega
      exact_mod_cast hc
    · refine Or.inr ⟨by omega, hsigns, ?_⟩
      have hc : ((univ.filter fun j => a j ≠ 0).card : ℤ) = 1 := by omega
      exact_mod_cast hc
  · intro hcases
    rcases hcases with ⟨hzero, hsigns, hcard⟩ | ⟨hroot, hsigns, hcard⟩
    · have hcount : ∑ j, (a j) ^ 2 = 4 * ((univ.filter fun j => a j ≠ 0).card : ℤ) := by
        rw [sum_sq_eq_sq_mul_card_support (c := 2) a hsigns]
        norm_num
      rw [hcard] at hcount
      have hbzero : ∑ j, (b j) ^ 2 = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [hzero j]; norm_num
      omega
    · have hcount : ∑ j, (a j) ^ 2 = 4 * ((univ.filter fun j => a j ≠ 0).card : ℤ) := by
        rw [sum_sq_eq_sq_mul_card_support (c := 2) a hsigns]
        norm_num
      rw [hcard] at hcount
      omega

/-- A norm-three vector of `E₈ ⊕ ℤ⁷` is
either a vector of `ℤ⁷` with three coordinates `±1`, or the sum of an `E₈` root
and a unit vector of `ℤ⁷`: `280 + 3360 = 3640` vectors. -/
theorem e8z7_norm_three_iff (v : Fin 15 → ℤ) :
    Matrix.toBilin' e8z7Gram v v = 3 ↔
      ((∀ j, Matrix.vecMul v e8z7Right j = 0) ∧
          (∀ j, Matrix.vecMul v e8z7Left j = 0 ∨ Matrix.vecMul v e8z7Left j = 2 ∨
            Matrix.vecMul v e8z7Left j = -2) ∧
          (univ.filter fun j => Matrix.vecMul v e8z7Left j ≠ 0).card = 3) ∨
        ((∑ j, (Matrix.vecMul v e8z7Right j) ^ 2 = 8) ∧
          (∀ j, Matrix.vecMul v e8z7Left j = 0 ∨ Matrix.vecMul v e8z7Left j = 2 ∨
            Matrix.vecMul v e8z7Left j = -2) ∧
          (univ.filter fun j => Matrix.vecMul v e8z7Left j ≠ 0).card = 1) := by
  rw [norm_three_iff_sum_sq e8z7Gram e8z7Coords 2 (by norm_num) e8z7Coords_gram v,
    e8z7_block_split v, show (3 : ℤ) * 2 ^ 2 = 12 by norm_num]
  exact e8z7_blocks_iff _ _ (e8z7Left_mem v) (e8z7Right_mem v)

end Lattice
end SRG266
