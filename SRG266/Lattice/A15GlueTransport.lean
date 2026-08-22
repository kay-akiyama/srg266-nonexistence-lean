/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.RootExtension
import SRG266.Lattice.Hosts.A15Plus

/-!
# Transport of the `A15` glue vector

The coordinate lattice `A15+` is obtained from `A15` by adjoining one vector
`x` whose fourth multiple is the standard numerator

`s = (1, 2, ..., 15)`

in the simple-root basis.  This file checks the root-inclusion and scaled
inverse matrices and proves that such a vector extends an abstract root
embedding to a matrix model of `A15+`.

No quotient classification occurs here.  The only host-specific fact left to
prove upstream is the existence of `x`; all pairing and surjectivity arguments
are supplied by `SRG266.Lattice.isMatrixModel_of_root_extension`.
-/

namespace SRG266
namespace Lattice

open scoped Matrix

/-- Inclusion of the `A15` simple-root basis into the generated basis of
`A15+`.  Columns are simple roots, rows are host-basis coordinates. -/
def a15RootInclusion : Matrix (Fin 15) (Fin 15) ℤ := fun i j =>
  if j = 0 then
    if i = 0 then 4 else if i = 1 then -2 else -1
  else if i = j then 1 else if i.1 = j.1 + 1 then -1 else 0

/-- Four times the inverse of `a15RootInclusion`. -/
def a15RootScaledInverse : Matrix (Fin 15) (Fin 15) ℤ := fun i j =>
  if j = 0 then i.1 + 1 else if j.1 ≤ i.1 then 4 else 0

/-- Retraction on the fourteen host basis vectors which already belong to the
root lattice. -/
def a15RootRetraction : Matrix (Fin 15) (Fin 15) ℤ := fun i j =>
  if j = 0 then 0 else if j.1 ≤ i.1 then 1 else 0

/-- Numerator of the order-four glue vector in the simple-root basis. -/
def a15GlueNumerator : Fin 15 → ℤ := fun i => i.1 + 1

/-- Rank-one correction which records the glue numerator in column zero. -/
def a15GlueCorrection : Matrix (Fin 15) (Fin 15) ℤ := fun i j =>
  if j = 0 then a15GlueNumerator i else 0

theorem a15RootInclusion_mul_scaledInverse :
    a15RootInclusion * a15RootScaledInverse =
      (4 : ℤ) • (1 : Matrix (Fin 15) (Fin 15) ℤ) := by
  decide +kernel

theorem a15RootInclusion_gram :
    a15RootInclusion.transpose * a15PlusGram * a15RootInclusion = gramA 15 := by
  decide +kernel

theorem a15RootRetraction_mul_inclusion :
    a15RootRetraction * a15RootInclusion + a15GlueCorrection =
      (1 : Matrix (Fin 15) (Fin 15) ℤ) := by
  decide +kernel

theorem a15GlueCorrection_mulVec (v : Fin 15 → ℤ) :
    a15GlueCorrection.mulVec v = v 0 • a15GlueNumerator := by
  funext i
  simp [a15GlueCorrection, Matrix.mulVec, dotProduct, a15GlueNumerator, mul_comm]

theorem a15RootInclusion_mulVec_zero (v : Fin 15 → ℤ) :
    a15RootInclusion.mulVec v 0 = 4 * v 0 := by
  simp only [a15RootInclusion, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [hj, Ne.symm hj]
  · simp

theorem a15Root_split (v : Fin 15 → ℤ) :
    a15RootRetraction.mulVec (a15RootInclusion.mulVec v) +
        v 0 • a15GlueNumerator = v := by
  have h := congrArg (fun M : Matrix (Fin 15) (Fin 15) ℤ => M.mulVec v)
    a15RootRetraction_mul_inclusion
  simpa [Matrix.add_mulVec, Matrix.mulVec_mulVec, a15GlueCorrection_mulVec]
    using h

/-- The linear extension determined by a fourth root of the standard glue
numerator. -/
noncomputable def a15GlueExtensionMap
    (L : PDUnimodularLattice 15)
    (f : (Fin 15 → ℤ) →ₗ[ℤ] L.carrier) (x : L.carrier) :
    (Fin 15 → ℤ) →ₗ[ℤ] L.carrier :=
  toZLinearMap
    { toFun := fun v => v 0 • x + f (a15RootRetraction.mulVec v)
      map_zero' := by simp
      map_add' := by
        intro v w
        simp only [Pi.add_apply, add_zsmul, Matrix.mulVec_add, map_add]
        abel }

theorem a15GlueExtensionMap_extends
    (L : PDUnimodularLattice 15)
    (f : (Fin 15 → ℤ) →ₗ[ℤ] L.carrier) (x : L.carrier)
    (hx : (4 : ℤ) • x = f a15GlueNumerator) (v : Fin 15 → ℤ) :
    a15GlueExtensionMap L f x (a15RootInclusion.mulVec v) = f v := by
  change a15RootInclusion.mulVec v 0 • x +
      f (a15RootRetraction.mulVec (a15RootInclusion.mulVec v)) = f v
  rw [a15RootInclusion_mulVec_zero]
  calc
    (4 * v 0) • x + f (a15RootRetraction.mulVec (a15RootInclusion.mulVec v)) =
        v 0 • ((4 : ℤ) • x) +
          f (a15RootRetraction.mulVec (a15RootInclusion.mulVec v)) := by
            rw [← mul_zsmul]
            congr 2
            ring
    _ = f (v 0 • a15GlueNumerator) +
          f (a15RootRetraction.mulVec (a15RootInclusion.mulVec v)) := by
            rw [hx, map_zsmul]
    _ = f (v 0 • a15GlueNumerator +
          a15RootRetraction.mulVec (a15RootInclusion.mulVec v)) := by
            rw [map_add]
    _ = f v := by
      congr 1
      rw [add_comm, a15Root_split]

/-- A normalized `A15` glue vector gives the complete coordinate model
`A15+`. -/
theorem isMatrixModel_a15Plus_of_glueVector
    (L : PDUnimodularLattice 15)
    (f : (Fin 15 → ℤ) →ₗ[ℤ] L.carrier)
    (hfpair : ∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' (gramA 15) v w)
    (x : L.carrier) (hx : (4 : ℤ) • x = f a15GlueNumerator) :
    IsMatrixModel L a15PlusGram := by
  apply isMatrixModel_of_root_extension L (gramA 15) a15PlusGram
    a15PlusGramInv a15RootInclusion a15RootScaledInverse 4
    (by norm_num) a15RootInclusion_mul_scaledInverse a15RootInclusion_gram
    a15PlusGram_mul_inv a15PlusGram_posDef f (a15GlueExtensionMap L f x)
    hfpair
  exact a15GlueExtensionMap_extends L f x hx

end Lattice
end SRG266
