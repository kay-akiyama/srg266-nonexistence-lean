/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.UnimodularEmbedding

/-!
# Extending a full-rank root embedding across glue

Let `P` be the inclusion matrix of a full-rank root lattice with Gram matrix
`A` into a unimodular coordinate lattice with Gram matrix `H`.  Suppose `Q`
is a scaled inverse, `P Q = d I`, and an abstract root embedding `f` extends
along `P` to a linear map `g` into an ambient unimodular lattice.

The extension condition alone forces `g` to preserve `H`: multiply two source
vectors by `d`, move them through `P Q`, and cancel `d²` in `ℤ`.  Positive
definiteness then makes `g` injective, while unimodularity makes it surjective
by `SRG266.Lattice.isMatrixModel_of_isometric_embedding_of_mul_eq_one`.

Thus the host-specific glue proofs only have to construct the extension map.
They do not have to prove its pairing formula, injectivity, surjectivity, or
the final coordinate-model statement.
-/

namespace SRG266
namespace Lattice

open scoped Matrix

/-- Pulling a bilinear form back along `P` has Gram matrix `Pᵀ H P`. -/
theorem toBilin'_mulVec_of_transpose_mul_mul
    {n : ℕ} (A H P : Matrix (Fin n) (Fin n) ℤ)
    (hgram : P.transpose * H * P = A) (v w : Fin n → ℤ) :
    Matrix.toBilin' H (P.mulVec v) (P.mulVec w) = Matrix.toBilin' A v w := by
  have hcomp := Matrix.toBilin'_comp H P P
  have happ := congrArg (fun B : LinearMap.BilinForm ℤ (Fin n → ℤ) => B v w) hcomp
  simpa [hgram] using happ

/-- A scaled right inverse acts as scalar multiplication on column vectors. -/
theorem mulVec_mulVec_eq_smul_of_mul_eq_smul_one
    {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℤ) (d : ℤ)
    (hinv : P * Q = d • (1 : Matrix (Fin n) (Fin n) ℤ)) (v : Fin n → ℤ) :
    P.mulVec (Q.mulVec v) = d • v := by
  rw [Matrix.mulVec_mulVec, hinv, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- **Root-extension transport.**  An extension of a full-rank root embedding
along a certified inclusion matrix is automatically an isometry onto the
stated unimodular coordinate model. -/
theorem isMatrixModel_of_root_extension
    {n : ℕ} (L : PDUnimodularLattice n)
    (A H Hinv P Q : Matrix (Fin n) (Fin n) ℤ) (d : ℤ)
    (hd : d ≠ 0)
    (hPQ : P * Q = d • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hgram : P.transpose * H * P = A)
    (hHinv : H * Hinv = 1)
    (hHpd : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < Matrix.toBilin' H v v)
    (f g : (Fin n → ℤ) →ₗ[ℤ] L.carrier)
    (hfpair : ∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' A v w)
    (hext : ∀ v, g (P.mulVec v) = f v) :
    IsMatrixModel L H := by
  have hscaled (v : Fin n → ℤ) : d • g v = f (Q.mulVec v) := by
    calc
      d • g v = g (d • v) := by rw [map_zsmul]
      _ = g (P.mulVec (Q.mulVec v)) := by
        rw [mulVec_mulVec_eq_smul_of_mul_eq_smul_one P Q d hPQ]
      _ = f (Q.mulVec v) := hext _
  have hgpair : ∀ v w, L.pairing (g v) (g w) = Matrix.toBilin' H v w := by
    intro v w
    have hmultiple : d ^ 2 * L.pairing (g v) (g w) =
        d ^ 2 * Matrix.toBilin' H v w := by
      calc
        d ^ 2 * L.pairing (g v) (g w) =
            L.pairing (d • g v) (d • g w) := by
              rw [map_zsmul, map_zsmul, LinearMap.smul_apply]
              simp only [zsmul_eq_mul, Int.cast_id]
              ring
        _ = L.pairing (f (Q.mulVec v)) (f (Q.mulVec w)) := by
              rw [hscaled v, hscaled w]
        _ = Matrix.toBilin' A (Q.mulVec v) (Q.mulVec w) := hfpair _ _
        _ = Matrix.toBilin' H (P.mulVec (Q.mulVec v))
              (P.mulVec (Q.mulVec w)) :=
            (toBilin'_mulVec_of_transpose_mul_mul A H P hgram _ _).symm
        _ = Matrix.toBilin' H (d • v) (d • w) := by
              rw [mulVec_mulVec_eq_smul_of_mul_eq_smul_one P Q d hPQ,
                mulVec_mulVec_eq_smul_of_mul_eq_smul_one P Q d hPQ]
        _ = d ^ 2 * Matrix.toBilin' H v w := by
              rw [map_zsmul, map_zsmul, LinearMap.smul_apply]
              simp only [zsmul_eq_mul, Int.cast_id]
              ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hd) hmultiple
  have hg : Function.Injective g := by
    intro v w hvw
    apply sub_eq_zero.mp
    by_contra hne
    have hpos := hHpd (v - w) hne
    have hzero : Matrix.toBilin' H (v - w) (v - w) = 0 := by
      rw [← hgpair]
      rw [map_sub, hvw, sub_self]
      simp
    omega
  exact isMatrixModel_of_isometric_embedding_of_mul_eq_one
    L H Hinv hHinv g hg hgpair

end Lattice
end SRG266
