/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.FullRankRootIndex

/-!
# Full-rank embeddings of unimodular lattices

An isometric embedding of a rank-`n` lattice with determinant one into a
rank-`n` unimodular lattice has index one.  Consequently it is already an
isometry onto the ambient lattice.

This elementary lemma is the final common step in all three full-rank glue
arguments.  Once a glue vector has been used to extend the root lattice to
one of the explicit unimodular Gram matrices, no separate surjectivity or
coordinate-cover argument is needed.
-/

namespace SRG266
namespace Lattice

/-- A full-rank isometric embedding whose source Gram determinant has absolute
value one is surjective. -/
theorem surjective_of_isometric_embedding_of_natAbs_det_eq_one
    {n : ℕ} (L : PDUnimodularLattice n)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (f : (Fin n → ℤ) →ₗ[ℤ] L.carrier)
    (hf : Function.Injective f)
    (hpair : ∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' A v w)
    (hdet : Int.natAbs A.det = 1) :
    Function.Surjective f := by
  have hindex :=
    quotient_card_sq_eq_natAbs_det_of_isometric_embedding_of_module
      L.carrier.isModule L.moduleFree L.moduleFinite L.pairing L.symmetric
        L.unimodular L.rank A f.toAddMonoidHom hf hpair
  rw [hdet] at hindex
  have hcard : Nat.card (L.carrier ⧸ f.toAddMonoidHom.range) = 1 := by
    rcases (pow_eq_one_iff.mp hindex) with h | h
    · exact h
    · norm_num at h
  have hsub : Subsingleton (L.carrier ⧸ f.toAddMonoidHom.range) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  intro y
  have hy : QuotientAddGroup.mk' f.toAddMonoidHom.range y =
      (0 : L.carrier ⧸ f.toAddMonoidHom.range) :=
    hsub.elim _ _
  have hymem : y ∈ f.toAddMonoidHom.range :=
    (QuotientAddGroup.eq_zero_iff y).mp hy
  exact hymem

/-- An isometric full-rank embedding of a determinant-one matrix exhibits the
ambient lattice as that matrix model. -/
theorem isMatrixModel_of_isometric_embedding_of_natAbs_det_eq_one
    {n : ℕ} (L : PDUnimodularLattice n)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (f : (Fin n → ℤ) →ₗ[ℤ] L.carrier)
    (hf : Function.Injective f)
    (hpair : ∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' A v w)
    (hdet : Int.natAbs A.det = 1) :
    IsMatrixModel L A := by
  have hsurj := surjective_of_isometric_embedding_of_natAbs_det_eq_one
    L A f hf hpair hdet
  exact ⟨LinearEquiv.ofBijective f ⟨hf, hsurj⟩, hpair⟩

/-- A checked integer inverse supplies the determinant-one hypothesis used by
`isMatrixModel_of_isometric_embedding_of_natAbs_det_eq_one`. -/
theorem isMatrixModel_of_isometric_embedding_of_mul_eq_one
    {n : ℕ} (L : PDUnimodularLattice n)
    (A Ainv : Matrix (Fin n) (Fin n) ℤ)
    (hinv : A * Ainv = 1)
    (f : (Fin n → ℤ) →ₗ[ℤ] L.carrier)
    (hf : Function.Injective f)
    (hpair : ∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' A v w) :
    IsMatrixModel L A := by
  have hdetUnit : IsUnit A.det := by
    apply IsUnit.of_mul_eq_one Ainv.det
    rw [← Matrix.det_mul, hinv, Matrix.det_one]
  exact isMatrixModel_of_isometric_embedding_of_natAbs_det_eq_one
    L A f hf hpair (Int.natAbs_of_isUnit hdetUnit)

end Lattice
end SRG266
