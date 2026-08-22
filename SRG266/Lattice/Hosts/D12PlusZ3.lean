/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.Rank15HostGramData
import SRG266.Lattice.HostCertificate
import SRG266.Lattice.Hosts.Model

/-!
# The core `D₁₂⁺` and the host `D₁₂⁺ ⊕ ℤ³`

Both lattices are presented with scale `2`: `2 • D₁₂⁺` is the same-parity model
`SRG266.Lattice.SameParitySumFour` on twelve coordinates, and the host adds a
`ℤ³` block, whose scaled coordinates are the even integers.

* `SRG266.Lattice.d12Plus_norm_three_iff` — a norm-three vector of
  `D₁₂⁺` is half-integral with all coordinates `±1/2`; there are `2048` of them;
* `SRG266.Lattice.d12Plus_even_coords_of_even_norm` — a vector of
  even norm is integral, because norms in the half-integral coset are odd;
* `SRG266.Lattice.d12PlusDoubleUnit` — lattice coefficients of the twelve
  vectors `2 e_j ∈ D₁₂` used by the projector bound;
* `SRG266.Lattice.d12PlusZ3Host : SRG266.OddUnimodularLattice15`;
* `SRG266.Lattice.d12PlusZ3_norm_three_iff` — the `3640` norm-three vectors of
  the host split as `2048` spinors, `1584` root-plus-unit vectors and `8`
  vectors inside `ℤ³`.
-/

namespace SRG266
namespace Lattice

open Finset

set_option maxRecDepth 8000

/-! ## The core `D₁₂⁺` -/

/-- Gram matrix of the generated basis of `D₁₂⁺`. -/
def d12PlusGram : Matrix (Fin 12) (Fin 12) ℤ :=
  fun i j => (d12PlusGramData.getD i.1 #[]).getD j.1 0

/-- Inverse of `d12PlusGram`. -/
def d12PlusGramInv : Matrix (Fin 12) (Fin 12) ℤ :=
  fun i j => (d12PlusGramInvData.getD i.1 #[]).getD j.1 0

/-- Lower factor of the LDLᵀ certificate of `d12PlusGram`. -/
def d12PlusLdltFactor : Matrix (Fin 12) (Fin 12) ℤ :=
  fun i j => (d12PlusLdltFactorData.getD i.1 #[]).getD j.1 0

/-- Weights of the LDLᵀ certificate of `d12PlusGram`. -/
def d12PlusLdltWeight : Fin 12 → ℤ :=
  fun k => d12PlusLdltWeightData.getD k.1 0

/-- Basis of `D₁₂⁺` in model coordinates, scaled by `2`. -/
def d12PlusCoords : Matrix (Fin 12) (Fin 12) ℤ :=
  fun i j => (d12PlusCoordsData.getD i.1 #[]).getD j.1 0

theorem d12PlusGram_entries_symm : ∀ i j, d12PlusGram i j = d12PlusGram j i := by
  decide +kernel

theorem d12PlusGram_isSymm : d12PlusGram.IsSymm :=
  isSymm_of_entries d12PlusGram d12PlusGram_entries_symm

theorem d12PlusGram_mul_inv : d12PlusGram * d12PlusGramInv = 1 :=
  mul_eq_one_of_entries d12PlusGram d12PlusGramInv (by decide +kernel)

theorem d12PlusGram_ldlt :
    checkIntegerScaledGram d12PlusGram d12PlusLdltFactor d12PlusLdltWeight
      d12PlusLdltScale = true := by
  decide +kernel

theorem d12PlusCoords_gram :
    ∀ i j, (d12PlusCoords * d12PlusCoords.transpose) i j = 2 ^ 2 * d12PlusGram i j := by
  decide +kernel

theorem d12PlusGram_posDef :
    ∀ v : Fin 12 → ℤ, v ≠ 0 → 0 < Matrix.toBilin' d12PlusGram v v :=
  toBilin'_posDef_of_ldlt d12PlusGram d12PlusGramInv d12PlusLdltFactor d12PlusLdltWeight
    d12PlusLdltScale d12PlusGram_isSymm d12PlusGram_mul_inv d12PlusGram_ldlt

theorem d12PlusCoords_row_parity :
    ∀ (i : Fin 12) (j : Fin 12), d12PlusCoords i j % 2 = d12PlusCoords i 0 % 2 := by
  decide +kernel

theorem d12PlusCoords_row_sum : ∀ i : Fin 12, (∑ j, d12PlusCoords i j) % 4 = 0 := by
  decide +kernel

theorem d12PlusCoords_row_mem (i : Fin 12) :
    (fun j => d12PlusCoords i j) ∈ sameParitySubmodule (Fin 12) := by
  refine ⟨⟨d12PlusCoords i 0, fun j => ?_⟩, ?_⟩
  · show (2 : ℤ) ∣ (d12PlusCoords i j - d12PlusCoords i 0)
    have h := d12PlusCoords_row_parity i j
    omega
  · show (4 : ℤ) ∣ ∑ j, d12PlusCoords i j
    have h := d12PlusCoords_row_sum i
    omega

/-- **The coordinate presentation of `D₁₂⁺`.** -/
theorem d12Plus_vecMul_mem (v : Fin 12 → ℤ) :
    SameParitySumFour (Matrix.vecMul v d12PlusCoords) :=
  vecMul_mem_submodule d12PlusCoords (sameParitySubmodule (Fin 12)) d12PlusCoords_row_mem v

/-- The `2048` norm-three vectors of `D₁₂⁺` are
exactly the half-integral ones, with all scaled coordinates `±1`. -/
theorem d12Plus_norm_three_iff (v : Fin 12 → ℤ) :
    Matrix.toBilin' d12PlusGram v v = 3 ↔
      ∀ j, Matrix.vecMul v d12PlusCoords j = 1 ∨ Matrix.vecMul v d12PlusCoords j = -1 := by
  rw [norm_three_iff_sum_sq d12PlusGram d12PlusCoords 2 (by norm_num) d12PlusCoords_gram v]
  set y := Matrix.vecMul v d12PlusCoords with hy
  constructor
  · intro hnorm
    exact sameParity_norm_three (by decide) (d12Plus_vecMul_mem v) (by rw [hnorm]; norm_num)
  · intro hsigns
    have hpoint : ∀ j, (y j) ^ 2 = 1 := by
      intro j
      rcases hsigns j with h | h <;> rw [h] <;> norm_num
    calc ∑ j, (y j) ^ 2 = ∑ _j : Fin 12, (1 : ℤ) :=
          Finset.sum_congr rfl fun j _ => hpoint j
      _ = 3 * 2 ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ]
          norm_num

/-- **The doubled unit vectors of `D₁₂`.**  Row `j` holds the coefficients, in
the generated basis, of the lattice vector `2 e_j`; its scale-two model
coordinates are `4 e_j`.  The matrix is `Coords ᵀ * Gram⁻¹`, the scaled left
inverse of the coordinate presentation, so no new certificate data is needed. -/
def d12PlusDoubleUnit : Matrix (Fin 12) (Fin 12) ℤ :=
  d12PlusCoords.transpose * d12PlusGramInv

theorem d12PlusCoords_mul_doubleUnit :
    d12PlusCoords * d12PlusDoubleUnit = (4 : ℤ) • (1 : Matrix (Fin 12) (Fin 12) ℤ) := by
  have hmat : d12PlusCoords * d12PlusCoords.transpose = (4 : ℤ) • d12PlusGram := by
    ext i j
    rw [d12PlusCoords_gram i j]
    norm_num
  rw [d12PlusDoubleUnit, ← Matrix.mul_assoc, hmat, Matrix.smul_mul,
    d12PlusGram_mul_inv]

theorem d12PlusDoubleUnit_mul_coords :
    d12PlusDoubleUnit * d12PlusCoords = (4 : ℤ) • (1 : Matrix (Fin 12) (Fin 12) ℤ) :=
  mul_eq_smul_one_comm (by norm_num) d12PlusCoords_mul_doubleUnit

/-- The model coordinates of the `j`-th doubled unit vector. -/
theorem d12PlusDoubleUnit_vecMul (j k : Fin 12) :
    Matrix.vecMul (fun l => d12PlusDoubleUnit j l) d12PlusCoords k =
      if j = k then 4 else 0 := by
  have h : (d12PlusDoubleUnit * d12PlusCoords) j k =
      ((4 : ℤ) • (1 : Matrix (Fin 12) (Fin 12) ℤ)) j k :=
    congrFun (congrFun d12PlusDoubleUnit_mul_coords j) k
  simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.one_apply,
    Matrix.smul_apply] using h

/-- A vector of
`D₁₂⁺` of even norm is integral: all its scaled coordinates are even.  Norms in
the half-integral coset `D₁₂ + s` are odd, so the centroid, of norm `300`,
cannot be a spinor. -/
theorem d12Plus_even_coords_of_even_norm (v : Fin 12 → ℤ) {m : ℤ}
    (hnorm : Matrix.toBilin' d12PlusGram v v = 2 * m) (j : Fin 12) :
    (2 : ℤ) ∣ Matrix.vecMul v d12PlusCoords j := by
  refine sameParity_even_of_dvd_eight (by simp) (d12Plus_vecMul_mem v) ?_ j
  rw [sum_sq_vecMul_coords d12PlusGram d12PlusCoords 2 d12PlusCoords_gram v, hnorm]
  exact ⟨m, by ring⟩

/-! ## The host `D₁₂⁺ ⊕ ℤ³` -/

/-- Index of the host model: three `ℤ` coordinates and twelve `D₁₂⁺`
coordinates. -/
abbrev D12PlusZ3Index := Fin 3 ⊕ Fin 12

/-- Linear position of a host coordinate in the generated data. -/
def d12PlusZ3Position : D12PlusZ3Index → ℕ :=
  Sum.elim (fun k => k.1) (fun k => 3 + k.1)

/-- Gram matrix of the generated basis of `D₁₂⁺ ⊕ ℤ³`. -/
def d12PlusZ3Gram : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => (d12PlusZ3GramData.getD i.1 #[]).getD j.1 0

/-- Inverse of `d12PlusZ3Gram`. -/
def d12PlusZ3GramInv : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => (d12PlusZ3GramInvData.getD i.1 #[]).getD j.1 0

/-- Lower factor of the LDLᵀ certificate of `d12PlusZ3Gram`. -/
def d12PlusZ3LdltFactor : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => (d12PlusZ3LdltFactorData.getD i.1 #[]).getD j.1 0

/-- Weights of the LDLᵀ certificate of `d12PlusZ3Gram`. -/
def d12PlusZ3LdltWeight : Fin 15 → ℤ :=
  fun k => d12PlusZ3LdltWeightData.getD k.1 0

/-- Basis of `D₁₂⁺ ⊕ ℤ³` in model coordinates, scaled by `2`. -/
def d12PlusZ3Coords : Matrix (Fin 15) D12PlusZ3Index ℤ :=
  fun i j => (d12PlusZ3CoordsData.getD i.1 #[]).getD (d12PlusZ3Position j) 0

/-- The `ℤ³` block of the coordinate matrix. -/
def d12PlusZ3Left : Matrix (Fin 15) (Fin 3) ℤ :=
  fun i j => d12PlusZ3Coords i (Sum.inl j)

/-- The `D₁₂⁺` block of the coordinate matrix. -/
def d12PlusZ3Right : Matrix (Fin 15) (Fin 12) ℤ :=
  fun i j => d12PlusZ3Coords i (Sum.inr j)

theorem d12PlusZ3Gram_entries_symm : ∀ i j, d12PlusZ3Gram i j = d12PlusZ3Gram j i := by
  decide +kernel

theorem d12PlusZ3Gram_isSymm : d12PlusZ3Gram.IsSymm :=
  isSymm_of_entries d12PlusZ3Gram d12PlusZ3Gram_entries_symm

theorem d12PlusZ3Gram_mul_inv : d12PlusZ3Gram * d12PlusZ3GramInv = 1 :=
  mul_eq_one_of_entries d12PlusZ3Gram d12PlusZ3GramInv (by decide +kernel)

theorem d12PlusZ3Gram_ldlt :
    checkIntegerScaledGram d12PlusZ3Gram d12PlusZ3LdltFactor d12PlusZ3LdltWeight
      d12PlusZ3LdltScale = true := by
  decide +kernel

theorem d12PlusZ3Coords_gram :
    ∀ i j, (d12PlusZ3Coords * d12PlusZ3Coords.transpose) i j = 2 ^ 2 * d12PlusZ3Gram i j := by
  decide +kernel

theorem d12PlusZ3Gram_posDef :
    ∀ v : Fin 15 → ℤ, v ≠ 0 → 0 < Matrix.toBilin' d12PlusZ3Gram v v :=
  toBilin'_posDef_of_ldlt d12PlusZ3Gram d12PlusZ3GramInv d12PlusZ3LdltFactor
    d12PlusZ3LdltWeight d12PlusZ3LdltScale d12PlusZ3Gram_isSymm d12PlusZ3Gram_mul_inv
    d12PlusZ3Gram_ldlt

/-- **The host `D₁₂⁺ ⊕ ℤ³`.** -/
noncomputable def d12PlusZ3Host : OddUnimodularLattice15 :=
  hostOfMatrix d12PlusZ3Gram d12PlusZ3GramInv d12PlusZ3Gram_isSymm d12PlusZ3Gram_mul_inv
    d12PlusZ3Gram_posDef (by decide +kernel)

/-! ## The coordinate model of the host -/

theorem d12PlusZ3Left_row_even : ∀ (i : Fin 15) (j : Fin 3), d12PlusZ3Left i j % 2 = 0 := by
  decide +kernel

theorem d12PlusZ3Right_row_parity :
    ∀ (i : Fin 15) (j : Fin 12), d12PlusZ3Right i j % 2 = d12PlusZ3Right i 0 % 2 := by
  decide +kernel

theorem d12PlusZ3Right_row_sum : ∀ i : Fin 15, (∑ j, d12PlusZ3Right i j) % 4 = 0 := by
  decide +kernel

theorem d12PlusZ3Left_mem (v : Fin 15 → ℤ) :
    ∀ j, (2 : ℤ) ∣ Matrix.vecMul v d12PlusZ3Left j := by
  refine vecMul_mem_submodule d12PlusZ3Left (scaleSubmodule 2 (Fin 3)) (fun i => ?_) v
  intro j
  show (2 : ℤ) ∣ d12PlusZ3Left i j
  have h := d12PlusZ3Left_row_even i j
  omega

theorem d12PlusZ3Right_mem (v : Fin 15 → ℤ) :
    SameParitySumFour (Matrix.vecMul v d12PlusZ3Right) := by
  refine vecMul_mem_submodule d12PlusZ3Right (sameParitySubmodule (Fin 12)) (fun i => ?_) v
  refine ⟨⟨d12PlusZ3Right i 0, fun j => ?_⟩, ?_⟩
  · show (2 : ℤ) ∣ (d12PlusZ3Right i j - d12PlusZ3Right i 0)
    have h := d12PlusZ3Right_row_parity i j
    omega
  · show (4 : ℤ) ∣ ∑ j, d12PlusZ3Right i j
    have h := d12PlusZ3Right_row_sum i
    omega

theorem d12PlusZ3_block_split (v : Fin 15 → ℤ) :
    ∑ j, (Matrix.vecMul v d12PlusZ3Coords j) ^ 2 =
      (∑ j, (Matrix.vecMul v d12PlusZ3Left j) ^ 2) +
        ∑ j, (Matrix.vecMul v d12PlusZ3Right j) ^ 2 := by
  rw [Fintype.sum_sum_type]
  rfl

/-- The block form of the norm-three condition: a `ℤ³` block with even entries
and a `2 • D₁₂⁺` block whose square sums add up to `12`. -/
theorem d12PlusZ3_blocks_iff (a : Fin 3 → ℤ) (b : Fin 12 → ℤ)
    (hleft : ∀ j, (2 : ℤ) ∣ a j) (hright : SameParitySumFour b) :
    (∑ j, (a j) ^ 2) + (∑ j, (b j) ^ 2) = 12 ↔
      ((∀ j, b j = 1 ∨ b j = -1) ∧ ∀ j, a j = 0) ∨
        ((∑ j, (b j) ^ 2 = 8) ∧ (∀ j, a j = 0 ∨ a j = 2 ∨ a j = -2) ∧
          (univ.filter fun j => a j ≠ 0).card = 1) ∨
        ((∀ j, b j = 0) ∧ (∀ j, a j = 0 ∨ a j = 2 ∨ a j = -2) ∧
          (univ.filter fun j => a j ≠ 0).card = 3) := by
  have hnn : (0 : ℤ) ≤ ∑ j, (a j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (a j)
  have hnn' : (0 : ℤ) ≤ ∑ j, (b j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (b j)
  constructor
  · intro htotal
    rcases hright.parity_cases with heven | hodd
    · -- the `D₁₂` block is integral, so its square sum is divisible by eight
      obtain ⟨k, hk⟩ := sum_sq_dvd_eight_of_even heven hright.2
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
      · refine Or.inr (Or.inr ⟨fun j => eq_zero_of_sum_sq_eq_zero b (by omega) j, hsigns, ?_⟩)
        have hc : ((univ.filter fun j => a j ≠ 0).card : ℤ) = 3 := by omega
        exact_mod_cast hc
      · refine Or.inr (Or.inl ⟨by omega, hsigns, ?_⟩)
        have hc : ((univ.filter fun j => a j ≠ 0).card : ℤ) = 1 := by omega
        exact_mod_cast hc
    · -- the `D₁₂⁺` block is half-integral, hence a spinor
      have hne : ∀ j, b j ≠ 0 := by
        intro j hj
        exact hodd j ⟨0, by rw [hj, mul_zero]⟩
      have hbig : (12 : ℤ) ≤ ∑ j, (b j) ^ 2 := by
        have hcard := card_le_sum_sq b hne
        simpa using hcard
      exact Or.inl ⟨sameParity_norm_three (by decide) hright (by omega),
        fun j => eq_zero_of_sum_sq_eq_zero a (by omega) j⟩
  · intro hcases
    have hzero3 : ∀ w : Fin 3 → ℤ, (∀ j, w j = 0) → ∑ j, (w j) ^ 2 = 0 := by
      intro w hw
      exact Finset.sum_eq_zero fun j _ => by rw [hw j]; norm_num
    have hzero12 : ∀ w : Fin 12 → ℤ, (∀ j, w j = 0) → ∑ j, (w j) ^ 2 = 0 := by
      intro w hw
      exact Finset.sum_eq_zero fun j _ => by rw [hw j]; norm_num
    rcases hcases with ⟨hspin, hzero⟩ | ⟨hroot, hsigns, hcard⟩ | ⟨hzero, hsigns, hcard⟩
    · have hb : ∑ j, (b j) ^ 2 = 12 := by
        have hpoint : ∀ j, (b j) ^ 2 = 1 := by
          intro j
          rcases hspin j with h | h <;> rw [h] <;> norm_num
        calc ∑ j, (b j) ^ 2 = ∑ _j : Fin 12, (1 : ℤ) :=
              Finset.sum_congr rfl fun j _ => hpoint j
          _ = 12 := by rw [Finset.sum_const, Finset.card_univ]; norm_num
      rw [hzero3 a hzero, hb]
      norm_num
    · have hcount : ∑ j, (a j) ^ 2 = 4 * ((univ.filter fun j => a j ≠ 0).card : ℤ) := by
        rw [sum_sq_eq_sq_mul_card_support (c := 2) a hsigns]
        norm_num
      rw [hcard] at hcount
      omega
    · have hcount : ∑ j, (a j) ^ 2 = 4 * ((univ.filter fun j => a j ≠ 0).card : ℤ) := by
        rw [sum_sq_eq_sq_mul_card_support (c := 2) a hsigns]
        norm_num
      rw [hcard] at hcount
      rw [hzero12 b hzero]
      omega

/-- The `3640` norm-three vectors of
the host are the `2048` spinors of `D₁₂⁺`, the `1584` sums of a `D₁₂` root and a
unit vector of `ℤ³`, and the `8` vectors with three coordinates `±1` inside
`ℤ³`. -/
theorem d12PlusZ3_norm_three_iff (v : Fin 15 → ℤ) :
    Matrix.toBilin' d12PlusZ3Gram v v = 3 ↔
      ((∀ j, Matrix.vecMul v d12PlusZ3Right j = 1 ∨ Matrix.vecMul v d12PlusZ3Right j = -1) ∧
          ∀ j, Matrix.vecMul v d12PlusZ3Left j = 0) ∨
        ((∑ j, (Matrix.vecMul v d12PlusZ3Right j) ^ 2 = 8) ∧
          (∀ j, Matrix.vecMul v d12PlusZ3Left j = 0 ∨ Matrix.vecMul v d12PlusZ3Left j = 2 ∨
            Matrix.vecMul v d12PlusZ3Left j = -2) ∧
          (univ.filter fun j => Matrix.vecMul v d12PlusZ3Left j ≠ 0).card = 1) ∨
        ((∀ j, Matrix.vecMul v d12PlusZ3Right j = 0) ∧
          (∀ j, Matrix.vecMul v d12PlusZ3Left j = 0 ∨ Matrix.vecMul v d12PlusZ3Left j = 2 ∨
            Matrix.vecMul v d12PlusZ3Left j = -2) ∧
          (univ.filter fun j => Matrix.vecMul v d12PlusZ3Left j ≠ 0).card = 3) := by
  rw [norm_three_iff_sum_sq d12PlusZ3Gram d12PlusZ3Coords 2 (by norm_num)
    d12PlusZ3Coords_gram v, d12PlusZ3_block_split v,
    show (3 : ℤ) * 2 ^ 2 = 12 by norm_num]
  exact d12PlusZ3_blocks_iff _ _ (d12PlusZ3Left_mem v) (d12PlusZ3Right_mem v)

end Lattice
end SRG266
