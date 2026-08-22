/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.RootExtension
import SRG266.Lattice.Hosts.E7E7PlusZ

/-!
# Transport of the diagonal `E7 + E7` glue vector

The unique integral nonzero discriminant class of `E7 + E7` is the diagonal
class.  This file presents its root inclusion explicitly and proves that a
single half-glue vector extends an abstract root embedding to the coordinate
model `(E7 + E7)+`.

The remaining upstream statement is only existence of that half-glue vector.
Pairing preservation, injectivity, surjectivity, and identification with the
checked host Gram matrix are derived here in Lean.
-/

namespace SRG266
namespace Lattice

open scoped Matrix

def e7e7RootInclusionData : Array (Array ℤ) :=
  #[#[4, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0],
    #[-2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-1, 0, -1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    #[-1, 0, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    #[-1, 0, 0, 0, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    #[-1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
    #[-2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, -1],
    #[0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 1, 0, 0, 1],
    #[0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 1, 0, 1],
    #[0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 1, 1],
    #[0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 1]]

def e7e7RootScaledInverseData : Array (Array ℤ) :=
  #[#[4, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0],
    #[8, 6, 4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0],
    #[12, 8, 8, 6, 6, 6, 6, 0, 0, 0, 0, 0, 0, 0],
    #[9, 6, 6, 6, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0],
    #[6, 4, 4, 4, 4, 2, 2, 0, 0, 0, 0, 0, 0, 0],
    #[3, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    #[7, 4, 4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0],
    #[4, 0, 0, 0, 0, 0, 0, 8, 2, 2, 2, 2, 2, 2],
    #[8, 0, 0, 0, 0, 0, 0, 16, 6, 4, 4, 4, 4, 4],
    #[12, 0, 0, 0, 0, 0, 0, 24, 8, 8, 6, 6, 6, 6],
    #[9, 0, 0, 0, 0, 0, 0, 18, 6, 6, 6, 4, 4, 4],
    #[6, 0, 0, 0, 0, 0, 0, 12, 4, 4, 4, 4, 2, 2],
    #[3, 0, 0, 0, 0, 0, 0, 6, 2, 2, 2, 2, 2, 0],
    #[7, 0, 0, 0, 0, 0, 0, 14, 4, 4, 4, 4, 4, 4]]

/-- Inclusion of the two `E7` simple-root bases into `(E7 + E7)+`. -/
def e7e7RootInclusion : Matrix (Fin 14) (Fin 14) ℤ :=
  matrixOfData e7e7RootInclusionData

/-- Twice the inverse of `e7e7RootInclusion`. -/
def e7e7RootScaledInverse : Matrix (Fin 14) (Fin 14) ℤ :=
  matrixOfData e7e7RootScaledInverseData

/-- The only non-root host basis vector is column zero. -/
def e7e7RootRetraction : Matrix (Fin 14) (Fin 14) ℤ := fun i j =>
  if j = 0 then 0 else e7e7RootScaledInverse i j / 2

/-- Numerator of the diagonal half-glue class. -/
def e7e7GlueNumerator : Fin 14 → ℤ := fun i => e7e7RootScaledInverse i 0

/-- The root-coordinate functional induced by the first host coordinate. -/
def e7e7GlueCoeffRow : Fin 14 → ℤ := fun j => e7e7RootInclusion 0 j / 2

def e7e7GlueCoeff (v : Fin 14 → ℤ) : ℤ :=
  dotProduct e7e7GlueCoeffRow v

def e7e7GlueCorrection : Matrix (Fin 14) (Fin 14) ℤ := fun i j =>
  e7e7GlueNumerator i * e7e7GlueCoeffRow j

theorem e7e7RootInclusion_mul_scaledInverse :
    e7e7RootInclusion * e7e7RootScaledInverse =
      (2 : ℤ) • (1 : Matrix (Fin 14) (Fin 14) ℤ) := by
  decide +kernel

theorem e7e7RootInclusion_gram :
    e7e7RootInclusion.transpose * e7e7PlusGram * e7e7RootInclusion =
      (adeGram [.E7, .E7]).2 := by
  decide +kernel

theorem e7e7RootRetraction_mul_inclusion :
    e7e7RootRetraction * e7e7RootInclusion + e7e7GlueCorrection =
      (1 : Matrix (Fin 14) (Fin 14) ℤ) := by
  decide +kernel

theorem e7e7RootInclusion_row_zero (j : Fin 14) :
    e7e7RootInclusion 0 j = 2 * e7e7GlueCoeffRow j := by
  fin_cases j <;> decide +kernel

theorem e7e7RootInclusion_mulVec_zero (v : Fin 14 → ℤ) :
    e7e7RootInclusion.mulVec v 0 = 2 * e7e7GlueCoeff v := by
  simp only [Matrix.mulVec, dotProduct, e7e7GlueCoeff]
  calc
    ∑ j, e7e7RootInclusion 0 j * v j =
        ∑ j, (2 * e7e7GlueCoeffRow j) * v j :=
      Finset.sum_congr rfl fun j _ => by rw [e7e7RootInclusion_row_zero]
    _ = 2 * ∑ j, e7e7GlueCoeffRow j * v j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring

theorem e7e7GlueCorrection_mulVec (v : Fin 14 → ℤ) :
    e7e7GlueCorrection.mulVec v = e7e7GlueCoeff v • e7e7GlueNumerator := by
  funext i
  simp only [Matrix.mulVec, dotProduct, e7e7GlueCorrection, e7e7GlueCoeff,
    Pi.smul_apply, smul_eq_mul]
  rw [mul_comm (∑ j, e7e7GlueCoeffRow j * v j) (e7e7GlueNumerator i)]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem e7e7Root_split (v : Fin 14 → ℤ) :
    e7e7RootRetraction.mulVec (e7e7RootInclusion.mulVec v) +
        e7e7GlueCoeff v • e7e7GlueNumerator = v := by
  have h := congrArg (fun M : Matrix (Fin 14) (Fin 14) ℤ => M.mulVec v)
    e7e7RootRetraction_mul_inclusion
  simpa [Matrix.add_mulVec, Matrix.mulVec_mulVec, e7e7GlueCorrection_mulVec]
    using h

noncomputable def e7e7GlueExtensionMap
    (L : PDUnimodularLattice 14)
    (f : (Fin 14 → ℤ) →ₗ[ℤ] L.carrier) (x : L.carrier) :
    (Fin 14 → ℤ) →ₗ[ℤ] L.carrier :=
  toZLinearMap
    { toFun := fun v => v 0 • x + f (e7e7RootRetraction.mulVec v)
      map_zero' := by simp
      map_add' := by
        intro v w
        simp only [Pi.add_apply, add_zsmul, Matrix.mulVec_add, map_add]
        abel }

theorem e7e7GlueExtensionMap_extends
    (L : PDUnimodularLattice 14)
    (f : (Fin 14 → ℤ) →ₗ[ℤ] L.carrier) (x : L.carrier)
    (hx : (2 : ℤ) • x = f e7e7GlueNumerator) (v : Fin 14 → ℤ) :
    e7e7GlueExtensionMap L f x (e7e7RootInclusion.mulVec v) = f v := by
  change e7e7RootInclusion.mulVec v 0 • x +
      f (e7e7RootRetraction.mulVec (e7e7RootInclusion.mulVec v)) = f v
  rw [e7e7RootInclusion_mulVec_zero]
  calc
    (2 * e7e7GlueCoeff v) • x +
        f (e7e7RootRetraction.mulVec (e7e7RootInclusion.mulVec v)) =
      e7e7GlueCoeff v • ((2 : ℤ) • x) +
        f (e7e7RootRetraction.mulVec (e7e7RootInclusion.mulVec v)) := by
          rw [← mul_zsmul]
          congr 2
          ring
    _ = f (e7e7GlueCoeff v • e7e7GlueNumerator) +
        f (e7e7RootRetraction.mulVec (e7e7RootInclusion.mulVec v)) := by
          rw [hx, map_zsmul]
    _ = f (e7e7GlueCoeff v • e7e7GlueNumerator +
        e7e7RootRetraction.mulVec (e7e7RootInclusion.mulVec v)) := by
          rw [map_add]
    _ = f v := by
      congr 1
      rw [add_comm, e7e7Root_split]

/-- A normalized diagonal half-glue vector gives the complete coordinate
model `(E7 + E7)+`. -/
theorem isMatrixModel_e7e7Plus_of_glueVector
    (L : PDUnimodularLattice 14)
    (f : (Fin 14 → ℤ) →ₗ[ℤ] L.carrier)
    (hfpair : ∀ v w, L.pairing (f v) (f w) =
      Matrix.toBilin' (adeGram [.E7, .E7]).2 v w)
    (x : L.carrier) (hx : (2 : ℤ) • x = f e7e7GlueNumerator) :
    IsMatrixModel L e7e7PlusGram := by
  apply isMatrixModel_of_root_extension L (adeGram [.E7, .E7]).2 e7e7PlusGram
    e7e7PlusGramInv e7e7RootInclusion e7e7RootScaledInverse 2
    (by norm_num) e7e7RootInclusion_mul_scaledInverse e7e7RootInclusion_gram
    e7e7PlusGram_mul_inv e7e7PlusGram_posDef f (e7e7GlueExtensionMap L f x)
    hfpair
  exact e7e7GlueExtensionMap_extends L f x hx

end Lattice
end SRG266
