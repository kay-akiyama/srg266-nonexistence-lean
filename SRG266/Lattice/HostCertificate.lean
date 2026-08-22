/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.HostBuilder
import SRG266.Certificates.LDLT

/-!
# Turning a Gram certificate into a host

`SRG266/Lattice/HostBuilder.lean` builds an `OddUnimodularLattice15` from a
symmetric invertible odd integer matrix whose form is positive definite.  This
file supplies the two services the generated data of
`SRG266/Certificates/Rank15HostGramData.lean` needs in order to meet that
interface, and the coordinate-model bridge used by the host reduction.

* `SRG266.Lattice.toBilin'_posDef_of_ldlt` upgrades an exact integer-scaled
  LDLᵀ certificate (`SRG266.checkIntegerScaledGram`) to *strict* positive
  definiteness, using only invertibility of the matrix.  The upgrade is the
  elementary Cauchy--Schwarz step: a positive-semidefinite form vanishing at `v`
  is orthogonal to everything at `v`, and an invertible Gram matrix has no
  radical.
* `SRG266.Lattice.toBilin'_mul_transpose` and
  `SRG266.Lattice.vecMul_coords_injective` are the model-presentation bridge.  A
  matrix `C` of *scaled* coordinate rows with `C * C.transpose = s ^ 2 • A` presents the
  lattice with Gram matrix `A` inside `ι → ℤ`: it multiplies all inner products
  by `s ^ 2` and is injective, with the explicit left inverse `C.transpose * A⁻¹`.
* `SRG266.Lattice.mul_eq_smul_one_comm` promotes a scaled right inverse of a
  square integer matrix to a scaled left inverse.  For a square coordinate
  presentation this turns `C * (C.transpose * A⁻¹) = s ^ 2 • 1`, which is
  immediate, into `(C.transpose * A⁻¹) * C = s ^ 2 • 1`, which exhibits explicit
  lattice coefficients for the scaled standard basis vectors.  No determinant is
  ever evaluated; only the adjugate identity is used.

The presentation sends a lattice vector to scaled coordinates lying in the
model (`vecMul_mem_submodule`), where the shell arithmetic of
`SRG266/Lattice/Hosts/Model.lean` applies.
-/

namespace SRG266
namespace Lattice

open scoped Matrix

section PosDef

variable {n : ℕ}

/-- The integer Gram form, read as a rational quadratic form. -/
theorem rationalQuadraticForm_intCast (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) :
    rationalQuadraticForm (fun i j => (A i j : ℚ)) (fun i => (v i : ℚ)) =
      ((Matrix.toBilin' A v v : ℤ) : ℚ) := by
  simp only [rationalQuadraticForm, Matrix.toBilin'_apply]
  push_cast
  rfl

/-- An exact integer-scaled LDLᵀ certificate makes the integer Gram form
nonnegative. -/
theorem toBilin'_nonneg_of_ldlt (A L : Matrix (Fin n) (Fin n) ℤ)
    (weight : Fin n → ℤ) (scale : ℤ)
    (hcheck : checkIntegerScaledGram A L weight scale = true) (v : Fin n → ℤ) :
    0 ≤ Matrix.toBilin' A v v := by
  have hrat := checkRationalLDLT_of_integer_scaled A L weight scale hcheck
  have hnn := rationalQuadraticForm_nonnegative_of_ldlt _ _ _ hrat (fun i => (v i : ℚ))
  rw [rationalQuadraticForm_intCast] at hnn
  exact_mod_cast hnn

/-- Expansion of the Gram form of a symmetric matrix along a line. -/
theorem toBilin'_add_smul (A : Matrix (Fin n) (Fin n) ℤ) (hsym : A.IsSymm)
    (v u : Fin n → ℤ) (t : ℤ) :
    Matrix.toBilin' A (t • v + u) (t • v + u) =
      t * t * Matrix.toBilin' A v v + 2 * t * Matrix.toBilin' A v u +
        Matrix.toBilin' A u u := by
  have hswap : Matrix.toBilin' A u v = Matrix.toBilin' A v u :=
    (toBilin'_isSymm A hsym).eq u v
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hswap]
  ring

/-- **Strict positive definiteness from a Gram certificate.**  An invertible
symmetric integer matrix with an exact integer-scaled LDLᵀ certificate has a
positive-definite Gram form.  This is the hypothesis shape of
`SRG266.hostOfMatrix`. -/
theorem toBilin'_posDef_of_ldlt (A Ainv L : Matrix (Fin n) (Fin n) ℤ)
    (weight : Fin n → ℤ) (scale : ℤ)
    (hsym : A.IsSymm) (hinv : A * Ainv = 1)
    (hcheck : checkIntegerScaledGram A L weight scale = true) :
    ∀ v : Fin n → ℤ, v ≠ 0 → 0 < Matrix.toBilin' A v v := by
  intro v hv
  have hnn := toBilin'_nonneg_of_ldlt A L weight scale hcheck
  rcases lt_or_eq_of_le (hnn v) with hpos | hzero
  · exact hpos
  exfalso
  -- the form vanishes at `v`, so `v` is orthogonal to every basis vector
  have horth : ∀ j : Fin n, Matrix.vecMul v A j = 0 := by
    intro j
    set u : Fin n → ℤ := Pi.single j 1 with hu
    have hvu : Matrix.toBilin' A v u = Matrix.vecMul v A j := by
      rw [toBilin'_eq_vecMul_dotProduct, hu, dotProduct_single, mul_one]
    have huu : 0 ≤ Matrix.toBilin' A u u := hnn u
    have hline : ∀ t : ℤ,
        0 ≤ 2 * t * Matrix.toBilin' A v u + Matrix.toBilin' A u u := by
      intro t
      have := hnn (t • v + u)
      rwa [toBilin'_add_smul A hsym v u t, ← hzero, mul_zero, zero_add] at this
    rw [← hvu]
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 := hline (Matrix.toBilin' A u u + 1)
      nlinarith [hline 0]
    · have h1 := hline (-(Matrix.toBilin' A u u + 1))
      nlinarith [hline 0]
  -- an invertible Gram matrix has no radical
  have hzero' : Matrix.vecMul v A = 0 := funext horth
  apply hv
  have : Matrix.vecMul (Matrix.vecMul v A) Ainv = Matrix.vecMul v (A * Ainv) :=
    Matrix.vecMul_vecMul v A Ainv
  rw [hzero', hinv, Matrix.vecMul_one, Matrix.zero_vecMul] at this
  exact this.symm

end PosDef

section Entries

variable {n : ℕ}

/-- Symmetry of a matrix, from its entries. -/
theorem isSymm_of_entries (A : Matrix (Fin n) (Fin n) ℤ) (h : ∀ i j, A i j = A j i) :
    A.IsSymm := by
  ext i j
  exact h j i

/-- A matrix product is the identity, from its entries. -/
theorem mul_eq_one_of_entries (A B : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i j, (A * B) i j = (1 : Matrix (Fin n) (Fin n) ℤ) i j) : A * B = 1 :=
  Matrix.ext h

/-- **A scaled right inverse is a scaled left inverse.**  For square integer
matrices `A * B = c • 1` with `c ≠ 0` already forces `B * A = c • 1`.

This is the only place a determinant of a coordinate matrix is mentioned: the
adjugate identity `adjugate A * A = det A • 1` cancels `A` on the left, and no
determinant is ever *evaluated*. -/
theorem mul_eq_smul_one_comm {A B : Matrix (Fin n) (Fin n) ℤ} {c : ℤ} (hc : c ≠ 0)
    (h : A * B = c • (1 : Matrix (Fin n) (Fin n) ℤ)) :
    B * A = c • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  have hdet : A.det * B.det = c ^ n := by
    have hd := congrArg Matrix.det h
    rwa [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at hd
  have hA : A.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact pow_ne_zero n hc hdet.symm
  have hkey : A * (B * A - c • (1 : Matrix (Fin n) (Fin n) ℤ)) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, sub_self]
  have hadj : A.det • (B * A - c • (1 : Matrix (Fin n) (Fin n) ℤ)) = 0 := by
    have hstep := congrArg (fun X : Matrix (Fin n) (Fin n) ℤ => A.adjugate * X) hkey
    simpa [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
      Matrix.one_mul] using hstep
  refine sub_eq_zero.mp ?_
  ext i j
  have hij := congrArg (fun X : Matrix (Fin n) (Fin n) ℤ => X i j) hadj
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hij
  rcases mul_eq_zero.mp hij with h0 | h0
  · exact absurd h0 hA
  · simpa using h0

end Entries

section Coordinates

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The dot product of a vector with itself is its square sum. -/
theorem dotProduct_self_eq_sum_sq (u : ι → ℤ) : dotProduct u u = ∑ i, (u i) ^ 2 := by
  simp [dotProduct, sq]

/-- The Gram matrix of a family of coordinate rows. -/
theorem toBilin'_mul_transpose (C : Matrix (Fin n) ι ℤ) (v w : Fin n → ℤ) :
    Matrix.toBilin' (C * C.transpose) v w =
      dotProduct (Matrix.vecMul v C) (Matrix.vecMul w C) := by
  have hleft : Matrix.toBilin' (C * C.transpose) v w =
      ∑ i, ∑ j, ∑ k, v i * C i k * (w j * C j k) := by
    simp only [Matrix.toBilin'_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have hright : dotProduct (Matrix.vecMul v C) (Matrix.vecMul w C) =
      ∑ k, ∑ i, ∑ j, v i * C i k * (w j * C j k) := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.vecMul_apply_eq_sum, Matrix.vecMul_apply_eq_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  rw [hleft, hright]
  calc (∑ i, ∑ j, ∑ k, v i * C i k * (w j * C j k))
      = ∑ i, ∑ k, ∑ j, v i * C i k * (w j * C j k) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, v i * C i k * (w j * C j k) := Finset.sum_comm

/-- Rows satisfying `C * C.transpose = s ^ 2 • A`
compute the Gram form of `A` up to the square of the coordinate scale. -/
theorem dotProduct_vecMul_coords (A : Matrix (Fin n) (Fin n) ℤ) (C : Matrix (Fin n) ι ℤ)
    (scale : ℤ) (hC : ∀ i j, (C * C.transpose) i j = scale ^ 2 * A i j) (v w : Fin n → ℤ) :
    dotProduct (Matrix.vecMul v C) (Matrix.vecMul w C) =
      scale ^ 2 * Matrix.toBilin' A v w := by
  rw [← toBilin'_mul_transpose C v w]
  have hmat : C * C.transpose = scale ^ 2 • A := by
    ext i j
    rw [hC i j]
    simp [Matrix.smul_apply]
  rw [hmat]
  simp only [Matrix.toBilin'_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The coordinate presentation is injective: `C.transpose * A⁻¹` recovers the
coefficients, scaled by `s ^ 2`. -/
theorem vecMul_coords_injective (A Ainv : Matrix (Fin n) (Fin n) ℤ)
    (C : Matrix (Fin n) ι ℤ) (scale : ℤ) (hscale : scale ≠ 0)
    (hinv : A * Ainv = 1) (hC : ∀ i j, (C * C.transpose) i j = scale ^ 2 * A i j) :
    Function.Injective fun v : Fin n → ℤ => Matrix.vecMul v C := by
  have hmat : C * C.transpose = scale ^ 2 • A := by
    ext i j
    rw [hC i j]
    simp [Matrix.smul_apply]
  intro v w hvw
  have hvw' : Matrix.vecMul v C = Matrix.vecMul w C := hvw
  have hstep : Matrix.vecMul v (C * C.transpose * Ainv) =
      Matrix.vecMul w (C * C.transpose * Ainv) := by
    simp only [← Matrix.vecMul_vecMul, hvw']
  rw [hmat, Matrix.smul_mul, hinv] at hstep
  have hv : (scale ^ 2) • v = (scale ^ 2) • w := by
    have hexpand : ∀ x : Fin n → ℤ,
        Matrix.vecMul x ((scale ^ 2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) =
          (scale ^ 2) • x := by
      intro x
      funext j
      simp [Matrix.vecMul, dotProduct, Matrix.smul_apply, Matrix.one_apply, mul_comm]
    rw [hexpand v, hexpand w] at hstep
    exact hstep
  have hne : (scale ^ 2 : ℤ) ≠ 0 := pow_ne_zero _ hscale
  funext j
  have := congrFun hv j
  simpa [Pi.smul_apply, smul_eq_mul, mul_right_inj' hne] using this

/-- The square sum of the coordinate image of `v` is the Gram norm of `v`,
scaled by `s ^ 2`. -/
theorem sum_sq_vecMul_coords (A : Matrix (Fin n) (Fin n) ℤ) (C : Matrix (Fin n) ι ℤ)
    (scale : ℤ) (hC : ∀ i j, (C * C.transpose) i j = scale ^ 2 * A i j) (v : Fin n → ℤ) :
    ∑ j, (Matrix.vecMul v C j) ^ 2 = scale ^ 2 * Matrix.toBilin' A v v := by
  rw [← dotProduct_self_eq_sum_sq, dotProduct_vecMul_coords A C scale hC]

/-- **Norm three in coordinates.**  A coordinate vector has Gram norm three
exactly when its scaled coordinate image has square sum `3 * s ^ 2`. -/
theorem norm_three_iff_sum_sq (A : Matrix (Fin n) (Fin n) ℤ) (C : Matrix (Fin n) ι ℤ)
    (scale : ℤ) (hscale : scale ≠ 0)
    (hC : ∀ i j, (C * C.transpose) i j = scale ^ 2 * A i j) (v : Fin n → ℤ) :
    Matrix.toBilin' A v v = 3 ↔ ∑ j, (Matrix.vecMul v C j) ^ 2 = 3 * scale ^ 2 := by
  rw [sum_sq_vecMul_coords A C scale hC v]
  have hne : (scale ^ 2 : ℤ) ≠ 0 := pow_ne_zero _ hscale
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    have : scale ^ 2 * Matrix.toBilin' A v v = scale ^ 2 * 3 := by
      rw [h]
      ring
    exact mul_left_cancel₀ hne this

omit [Fintype ι] in
/-- The coordinate image of a lattice vector lies in any submodule containing
the coordinate rows. -/
theorem vecMul_mem_submodule (C : Matrix (Fin n) ι ℤ) (M : Submodule ℤ (ι → ℤ))
    (hrows : ∀ i, (fun j => C i j) ∈ M) (v : Fin n → ℤ) : Matrix.vecMul v C ∈ M := by
  have hcombination : Matrix.vecMul v C = ∑ i, v i • (fun j => C i j) := by
    funext j
    rw [Matrix.vecMul_apply_eq_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply]
  rw [hcombination]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hrows i)

end Coordinates

end Lattice
end SRG266
