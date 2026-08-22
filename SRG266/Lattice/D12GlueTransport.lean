/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.RootExtension
import SRG266.Lattice.Hosts.D12PlusZ3

/-!
# Transport of a `D12` spinor glue vector

This file gives the root inclusion `D12 ⊂ D12+` in the generated host basis.
It proves that a single vector whose double is the standard spinor numerator
extends an abstract `D12` root embedding to the checked coordinate model
`D12+`.

The other spinor class is related by the usual `D12` diagram automorphism.
Consequently the upstream glue argument only needs to normalize one of the two
spinor classes and produce this half-vector.
-/

namespace SRG266
namespace Lattice

open scoped Matrix

def d12RootInclusionData : Array (Array ℤ) :=
  #[#[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-1, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-1, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
    #[-1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0],
    #[-1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
    #[-1, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
    #[-1, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0],
    #[-1, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
    #[-1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1],
    #[5, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0]]

def d12RootScaledInverseData : Array (Array ℤ) :=
  #[#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[3, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[4, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    #[5, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0],
    #[6, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0],
    #[7, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0],
    #[8, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0],
    #[9, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0],
    #[10, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0],
    #[5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2],
    #[6, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]]

def d12RootInclusion : Matrix (Fin 12) (Fin 12) ℤ :=
  matrixOfData d12RootInclusionData

/-- Twice the inverse of `d12RootInclusion`. -/
def d12RootScaledInverse : Matrix (Fin 12) (Fin 12) ℤ :=
  matrixOfData d12RootScaledInverseData

def d12RootRetraction : Matrix (Fin 12) (Fin 12) ℤ := fun i j =>
  if j = 0 then 0 else d12RootScaledInverse i j / 2

/-- Numerator of the chosen `D12` spinor class. -/
def d12GlueNumerator : Fin 12 → ℤ := fun i => d12RootScaledInverse i 0

def d12GlueCorrection : Matrix (Fin 12) (Fin 12) ℤ := fun i j =>
  if j = 0 then d12GlueNumerator i else 0

theorem d12RootInclusion_mul_scaledInverse :
    d12RootInclusion * d12RootScaledInverse =
      (2 : ℤ) • (1 : Matrix (Fin 12) (Fin 12) ℤ) := by
  decide +kernel

theorem d12RootInclusion_gram :
    d12RootInclusion.transpose * d12PlusGram * d12RootInclusion = gramD 12 := by
  decide +kernel

theorem d12RootRetraction_mul_inclusion :
    d12RootRetraction * d12RootInclusion + d12GlueCorrection =
      (1 : Matrix (Fin 12) (Fin 12) ℤ) := by
  decide +kernel

theorem d12GlueCorrection_mulVec (v : Fin 12 → ℤ) :
    d12GlueCorrection.mulVec v = v 0 • d12GlueNumerator := by
  funext i
  simp [d12GlueCorrection, Matrix.mulVec, dotProduct, d12GlueNumerator, mul_comm]

theorem d12RootInclusion_mulVec_zero (v : Fin 12 → ℤ) :
    d12RootInclusion.mulVec v 0 = 2 * v 0 := by
  simp only [d12RootInclusion, matrixOfData, d12RootInclusionData,
    Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single 0]
  · norm_num
  · intro j _ hj
    fin_cases j <;> simp_all
  · simp

theorem d12Root_split (v : Fin 12 → ℤ) :
    d12RootRetraction.mulVec (d12RootInclusion.mulVec v) +
        v 0 • d12GlueNumerator = v := by
  have h := congrArg (fun M : Matrix (Fin 12) (Fin 12) ℤ => M.mulVec v)
    d12RootRetraction_mul_inclusion
  simpa [Matrix.add_mulVec, Matrix.mulVec_mulVec, d12GlueCorrection_mulVec]
    using h

noncomputable def d12GlueExtensionMap
    (L : PDUnimodularLattice 12)
    (f : (Fin 12 → ℤ) →ₗ[ℤ] L.carrier) (x : L.carrier) :
    (Fin 12 → ℤ) →ₗ[ℤ] L.carrier :=
  toZLinearMap
    { toFun := fun v => v 0 • x + f (d12RootRetraction.mulVec v)
      map_zero' := by simp
      map_add' := by
        intro v w
        simp only [Pi.add_apply, add_zsmul, Matrix.mulVec_add, map_add]
        abel }

theorem d12GlueExtensionMap_extends
    (L : PDUnimodularLattice 12)
    (f : (Fin 12 → ℤ) →ₗ[ℤ] L.carrier) (x : L.carrier)
    (hx : (2 : ℤ) • x = f d12GlueNumerator) (v : Fin 12 → ℤ) :
    d12GlueExtensionMap L f x (d12RootInclusion.mulVec v) = f v := by
  change d12RootInclusion.mulVec v 0 • x +
      f (d12RootRetraction.mulVec (d12RootInclusion.mulVec v)) = f v
  rw [d12RootInclusion_mulVec_zero]
  calc
    (2 * v 0) • x + f (d12RootRetraction.mulVec (d12RootInclusion.mulVec v)) =
      v 0 • ((2 : ℤ) • x) +
        f (d12RootRetraction.mulVec (d12RootInclusion.mulVec v)) := by
          rw [← mul_zsmul]
          congr 2
          ring
    _ = f (v 0 • d12GlueNumerator) +
        f (d12RootRetraction.mulVec (d12RootInclusion.mulVec v)) := by
          rw [hx, map_zsmul]
    _ = f (v 0 • d12GlueNumerator +
        d12RootRetraction.mulVec (d12RootInclusion.mulVec v)) := by
          rw [map_add]
    _ = f v := by
      congr 1
      rw [add_comm, d12Root_split]

/-- A normalized `D12` spinor half-vector gives the complete coordinate model
`D12+`. -/
theorem isMatrixModel_d12Plus_of_glueVector
    (L : PDUnimodularLattice 12)
    (f : (Fin 12 → ℤ) →ₗ[ℤ] L.carrier)
    (hfpair : ∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' (gramD 12) v w)
    (x : L.carrier) (hx : (2 : ℤ) • x = f d12GlueNumerator) :
    IsMatrixModel L d12PlusGram := by
  apply isMatrixModel_of_root_extension L (gramD 12) d12PlusGram
    d12PlusGramInv d12RootInclusion d12RootScaledInverse 2
    (by norm_num) d12RootInclusion_mul_scaledInverse d12RootInclusion_gram
    d12PlusGram_mul_inv d12PlusGram_posDef f (d12GlueExtensionMap L f x)
    hfpair
  exact d12GlueExtensionMap_extends L f x hx

end Lattice
end SRG266
