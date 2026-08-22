/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.FullRankGlueArithmetic
import SRG266.Lattice.RootLatticeCertsA
import SRG266.Lattice.RootLatticeCertsD
import SRG266.Lattice.RootLatticeCertsE
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# Index of a full-rank root embedding

For an isometric full-rank embedding with Gram matrix `A` into a unimodular
lattice `L`, the index of the image has square `det A`.  This is the abstract
lattice step common to all three remaining glue cases.

The proof is basis-free at the interface.  Internally it chooses a basis of
`L`, writes the embedding matrix as `M` and the ambient pairing matrix as `H`,
and uses

`A = Mᵀ H M`,  `|det H| = 1`,  `[L : image] = |det M|`.
-/

namespace SRG266
namespace Lattice

open scoped Matrix
open Module

/-- **Index-square formula for a full-rank isometric embedding into a
unimodular lattice.**  The module instance is explicit for the same reason as
in `SRG266.Lattice.exists_pdCore_of_module`: a bundled `ModuleCat` carrier and
the canonical integer module are propositionally, but not definitionally,
equal. -/
theorem quotient_card_sq_eq_natAbs_det_of_isometric_embedding_of_module
    {X : Type*} [AddCommGroup X] (instMod : Module ℤ X)
    (instFree : @Module.Free ℤ X _ _ instMod)
    (instFinite : @Module.Finite ℤ X _ _ instMod)
    (B : @LinearMap.BilinForm ℤ _ X _ instMod)
    (hsymm : B.IsSymm) (hunimod : Function.Bijective B)
    {n : ℕ} (hrank : @Module.finrank ℤ X _ _ instMod = n)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (f : (Fin n → ℤ) →+ X)
    (hf : Function.Injective f)
    (hpair : ∀ v w, B (f v) (f w) = Matrix.toBilin' A v w) :
    Nat.card (X ⧸ f.range) ^ 2 = Int.natAbs A.det := by
  classical
  have hinst : instMod = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  subst hinst
  letI := instFree
  letI := instFinite
  let flin : (Fin n → ℤ) →ₗ[ℤ] X := f.toIntLinearMap
  let std : Basis (Fin n) ℤ (Fin n → ℤ) := Pi.basisFun ℤ (Fin n)
  let b : Basis (Fin n) ℤ X := Module.finBasisOfFinrankEq ℤ X hrank
  have hrangeSub : LinearMap.range flin = f.range.toIntSubmodule := by
    ext x
    simp [flin]
  let e := (LinearEquiv.ofInjective flin hf).trans
    (LinearEquiv.ofEq _ _ hrangeSub)
  let bN := std.map e
  let M : Matrix (Fin n) (Fin n) ℤ := LinearMap.toMatrix std b flin
  let H : Matrix (Fin n) (Fin n) ℤ := B.toMatrix b

  have hform : B.comp flin flin = Matrix.toBilin' A := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact hpair v w
  have hmatrix : M.transpose * H * M = A := by
    calc
      M.transpose * H * M = (B.comp flin flin).toMatrix std := by
        simpa [M, H] using (B.toMatrix_comp b std flin flin).symm
      _ = (Matrix.toBilin' A).toMatrix std := by rw [hform]
      _ = A := by
        simp [std, LinearMap.BilinForm.toMatrix_basisFun]

  let p : X ≃ₗ[ℤ] Module.Dual ℤ X := LinearEquiv.ofBijective B hunimod
  let P : Matrix (Fin n) (Fin n) ℤ :=
    LinearMap.toMatrix b b.dualBasis p
  let Q : Matrix (Fin n) (Fin n) ℤ :=
    LinearMap.toMatrix b.dualBasis b p.symm
  have hPQ : P * Q = 1 := by
    rw [← LinearMap.toMatrix_comp, LinearEquiv.comp_coe,
      p.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.toMatrix_id]
  have hdetP_unit : IsUnit P.det := by
    apply IsUnit.of_mul_eq_one Q.det
    rw [← Matrix.det_mul, hPQ, Matrix.det_one]
  have hPH : P = H := by
    ext i j
    simp [P, H, p, LinearMap.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply, hsymm.eq]
  have hdetH : Int.natAbs H.det = 1 := by
    rw [← hPH]
    exact Int.natAbs_of_isUnit hdetP_unit

  have hbN_apply (j : Fin n) : (bN j : X) = flin (std j) := by
    simp [bN, e]
  have hcard : Int.natAbs M.det = Nat.card (X ⧸ f.range) := by
    have hc := AddSubgroup.index_eq_natAbs_det b f.range bN
    rw [AddSubgroup.index] at hc
    rw [hc]
    congr 1
    rw [Basis.det_apply]
    congr 1
    ext i j
    simp only [M, LinearMap.toMatrix_apply, Basis.toMatrix_apply]
    change (b.repr (flin (std j))) i = (b.repr (bN j : X)) i
    rw [hbN_apply]

  have hdet : A.det = M.det * H.det * M.det := by
    rw [← hmatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [← hcard]
  rw [hdet, Int.natAbs_mul, Int.natAbs_mul, hdetH]
  ring

/-! ## Application to the root-embedding boundary -/

/-- A singleton ADE block is its ordinary Cartan matrix. -/
theorem adeGram_singleton (t : ADEType) : (adeGram [t]).2 = t.gram := by
  ext i j
  simp [adeGram, adeEntry, ADEType.gram]

/-- A full-rank ADE root embedding has index squared equal to the determinant
of its ADE Gram matrix.  The witness is returned because the root-embedding
interface is existential. -/
theorem IsRootADEEmbedding.exists_image_index {n : ℕ}
    (L : PDUnimodularLattice n) (ts : List ADEType)
    (hrank : ADEType.rankSum ts = n) (h : IsRootADEEmbedding L ts) :
    ∃ f : (Fin (ADEType.rankSum ts) → ℤ) →ₗ[ℤ] L.carrier,
      Function.Injective f ∧
        (∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' (adeGram ts).2 v w) ∧
        Nat.card (L.carrier ⧸ f.toAddMonoidHom.range) ^ 2 =
          Int.natAbs (adeGram ts).2.det := by
  obtain ⟨f, hf, hpair, _hroots⟩ := h
  refine ⟨f, hf, hpair, ?_⟩
  exact quotient_card_sq_eq_natAbs_det_of_isometric_embedding_of_module
    L.carrier.isModule L.moduleFree L.moduleFinite L.pairing L.symmetric
      L.unimodular (L.rank.trans hrank.symm) (adeGram ts).2
      f.toAddMonoidHom hf hpair

/-- A full-rank `D12` root lattice has index two in its unimodular
overlattice. -/
theorem IsRootADEEmbedding.exists_d12_image_index_two
    (L : PDUnimodularLattice 12) (h : IsRootADEEmbedding L [.D 12]) :
    ∃ f : (Fin (ADEType.rankSum [.D 12]) → ℤ) →ₗ[ℤ] L.carrier,
      Function.Injective f ∧ Nat.card (L.carrier ⧸ f.toAddMonoidHom.range) = 2 := by
  obtain ⟨f, hf, _hpair, hindex⟩ := h.exists_image_index L [.D 12] rfl
  have hdet : (adeGram [.D 12]).2.det = 4 := by
    calc
      (adeGram [.D 12]).2.det = (ADEType.D 12).gram.det :=
        congrArg Matrix.det (adeGram_singleton (.D 12))
      _ = 4 := by rw [det_gram_d12]; rfl
  rw [hdet] at hindex
  norm_num at hindex
  refine ⟨f, hf, Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) ?_⟩
  simpa using hindex

/-- The determinant of the two-block `E7 + E7` Cartan matrix is four. -/
theorem det_adeGram_e7_e7 : (adeGram [.E7, .E7]).2.det = 4 := by
  let e : Fin 14 ≃ Fin 7 ⊕ Fin 7 := (finSumFinEquiv : Fin 7 ⊕ Fin 7 ≃ Fin 14).symm
  have hblocks : Matrix.reindex e e (adeGram [.E7, .E7]).2 =
      Matrix.fromBlocks (gramE 7) 0 0 (gramE 7) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [e, adeGram, adeEntry, ADEType.rank, ADEType.gramEntry, gramE,
        Matrix.reindex_apply,
        Matrix.submatrix, finSumFinEquiv]
  calc
    (adeGram [.E7, .E7]).2.det =
        (Matrix.reindex e e (adeGram [.E7, .E7]).2).det :=
      (Matrix.det_reindex_self e (adeGram [.E7, .E7]).2).symm
    _ = (Matrix.fromBlocks (gramE 7) 0 0 (gramE 7)).det := congrArg Matrix.det hblocks
    _ = (gramE 7).det * (gramE 7).det := Matrix.det_fromBlocks_zero₂₁ _ _ _
    _ = 4 := by rw [det_e7]; decide

/-- A full-rank `E7 + E7` root lattice has index two in its unimodular
overlattice. -/
theorem IsRootADEEmbedding.exists_e7e7_image_index_two
    (L : PDUnimodularLattice 14) (h : IsRootADEEmbedding L [.E7, .E7]) :
    ∃ f : (Fin (ADEType.rankSum [.E7, .E7]) → ℤ) →ₗ[ℤ] L.carrier,
      Function.Injective f ∧ Nat.card (L.carrier ⧸ f.toAddMonoidHom.range) = 2 := by
  obtain ⟨f, hf, _hpair, hindex⟩ := h.exists_image_index L [.E7, .E7] rfl
  rw [det_adeGram_e7_e7] at hindex
  norm_num at hindex
  refine ⟨f, hf, Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) ?_⟩
  simpa using hindex

/-- A full-rank `A15` root lattice has index four in its unimodular
overlattice. -/
theorem IsRootADEEmbedding.exists_a15_image_index_four
    (L : PDUnimodularLattice 15) (h : IsRootADEEmbedding L [.A 15]) :
    ∃ f : (Fin (ADEType.rankSum [.A 15]) → ℤ) →ₗ[ℤ] L.carrier,
      Function.Injective f ∧ Nat.card (L.carrier ⧸ f.toAddMonoidHom.range) = 4 := by
  obtain ⟨f, hf, _hpair, hindex⟩ := h.exists_image_index L [.A 15] rfl
  have hdet : (adeGram [.A 15]).2.det = 16 := by
    calc
      (adeGram [.A 15]).2.det = (ADEType.A 15).gram.det :=
        congrArg Matrix.det (adeGram_singleton (.A 15))
      _ = 16 := by rw [det_gram_a15]; rfl
  rw [hdet] at hindex
  norm_num at hindex
  refine ⟨f, hf, Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) ?_⟩
  simpa using hindex

end Lattice
end SRG266
