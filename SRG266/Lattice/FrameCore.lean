/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Branches.PureCore

/-!
# Frame complements

The orthogonal complement of a norm-one frame in a rank-15 unimodular lattice
is a positive-definite unimodular lattice of rank `15 - k`. This module bundles
that complement, its matrix models, and the transport back to
`SRG266.Lattice.IsHostCoreModel`.
-/

namespace SRG266

/-- A positive-definite unimodular integral lattice of rank `n`. -/
structure PDUnimodularLattice (n : ℕ) where
  /-- The underlying `ℤ`-module, bundled so that its instances stay available. -/
  carrier : ModuleCat ℤ
  [moduleFree : Module.Free ℤ carrier]
  [moduleFinite : Module.Finite ℤ carrier]
  /-- The integral bilinear form. -/
  pairing : LinearMap.BilinForm ℤ carrier
  /-- The form is symmetric. -/
  symmetric : pairing.IsSymm
  /-- The form is positive definite. -/
  positiveDefinite : ∀ v : carrier, v ≠ 0 → 0 < pairing v v
  /-- The form is unimodular, stated as bijectivity of the adjoint. -/
  unimodular : Function.Bijective pairing
  /-- The rank is `n`. -/
  rank : Module.finrank ℤ carrier = n

namespace Lattice

/-! ## Coordinate models -/

/-- **An isometry onto the coordinate lattice of an integer Gram matrix.**

This is the shape in which a classification theorem states its conclusion, and
the shape `SRG266.RootedCorankFourClassification` uses.  It is strictly more
than `SRG266.Lattice.IsHostCoreModel` asks for: surjectivity of the isometry is
what supplies the *cover* clause there. -/
def IsMatrixModel {n m : ℕ} (L : PDUnimodularLattice n)
    (A : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∃ f : (Fin m → ℤ) ≃ₗ[ℤ] L.carrier,
    ∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' A v w

/-- **A `PDUnimodularLattice` from an integer matrix**, the counterpart of
`SRG266.hostOfMatrix` with the rank a parameter and no oddness clause.  The
hypotheses are the shape the repository's `SRG266/Certificates/LDLT.lean`
machinery produces, so the three Gram matrices of
`SRG266.RootedCorankFourClassification` all satisfy them
(`SRG266.Lattice.d12PlusGram_posDef` and `…_mul_inv`, and their two
companions). -/
noncomputable def pdLatticeOfMatrix {n : ℕ} (A Ainv : Matrix (Fin n) (Fin n) ℤ)
    (hsym : A.IsSymm) (hinv : A * Ainv = 1)
    (hpd : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < Matrix.toBilin' A v v) :
    PDUnimodularLattice n where
  carrier := ModuleCat.of ℤ (Fin n → ℤ)
  pairing := Matrix.toBilin' A
  symmetric := toBilin'_isSymm A hsym
  positiveDefinite := hpd
  unimodular := toBilin'_bijective_of_mul_eq_one A Ainv hinv
  rank := Module.finrank_fin_fun ℤ

/-- **Neither definition above is vacuous.**  The coordinate lattice of `A` is a
`SRG266.PDUnimodularLattice` and is a matrix model of `A`, by the identity
isometry. -/
theorem isMatrixModel_pdLatticeOfMatrix {n : ℕ} (A Ainv : Matrix (Fin n) (Fin n) ℤ)
    (hsym : A.IsSymm) (hinv : A * Ainv = 1)
    (hpd : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < Matrix.toBilin' A v v) :
    IsMatrixModel (pdLatticeOfMatrix A Ainv hsym hinv hpd) A :=
  ⟨LinearEquiv.refl ℤ (Fin n → ℤ), fun _ _ => rfl⟩

/-! ## Additive maps are `ℤ`-linear, for any module instances -/

/-- **An additive map between `ℤ`-modules is `ℤ`-linear.**  Stated for
arbitrary `Module ℤ` instances rather than for the canonical
`AddCommGroup.toIntModule`, which is what lets a map produced by the abstract
theory of `SRG266/Lattice/Core.lean` be used against a bundled `ModuleCat ℤ`
carrier.  The proof is `Subsingleton.elim` on the two instances followed by
`map_zsmul`. -/
def toZLinearMap {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [instA : Module ℤ A] [instB : Module ℤ B] (f : A →+ B) : A →ₗ[ℤ] B where
  toFun := f
  map_add' := f.map_add
  map_smul' := by
    have hA : instA = AddCommGroup.toIntModule A := Subsingleton.elim _ _
    have hB : instB = AddCommGroup.toIntModule B := Subsingleton.elim _ _
    subst hA
    subst hB
    intro r x
    simp

@[simp]
theorem toZLinearMap_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (f : A →+ B) (a : A) : toZLinearMap f a = f a := rfl

/-! ## The frame complement is a lattice -/

/-- **The frame complement, for an unbundled module instance.**

Let `pairing` be a positive-definite unimodular symmetric integral form of rank
`n` on `X` and let `u` be an orthonormal family of `k` vectors whose orthogonal
complement carries no norm-one vector.  Then that complement is a
`SRG266.PDUnimodularLattice (n - k)`, and it sits inside `X` by a
pairing-preserving additive map whose image is exactly the set of vectors
orthogonal to every `u i`.

The module instance is an explicit argument so that a bundled `ModuleCat ℤ`
carrier can be passed; see the module docstring. -/
theorem exists_pdCore_of_module {X : Type} [AddCommGroup X] (instMod : Module ℤ X)
    (pairing : @LinearMap.BilinForm ℤ _ X _ instMod)
    (instFree : @Module.Free ℤ X _ _ instMod)
    (instFinite : @Module.Finite ℤ X _ _ instMod)
    (hsymm : pairing.IsSymm)
    (hpd : ∀ v : X, v ≠ 0 → 0 < pairing v v)
    (hbij : Function.Bijective pairing)
    {n : ℕ} (hrank : @Module.finrank ℤ X _ _ instMod = n)
    {k : ℕ} (u : Fin k → X)
    (hnorm : ∀ i, pairing (u i) (u i) = 1)
    (horth : ∀ i j, i ≠ j → pairing (u i) (u j) = 0)
    (hfree : ∀ w : X, (∀ i, pairing (u i) w = 0) → pairing w w ≠ 1) :
    ∃ (L₀ : PDUnimodularLattice (n - k)) (ι : L₀.carrier →+ X),
      (∀ v w : L₀.carrier, pairing (ι v) (ι w) = L₀.pairing v w) ∧
      (∀ y : X, (∀ i, pairing (u i) y = 0) → ∃ z : L₀.carrier, ι z = y) ∧
      (∀ v : L₀.carrier, L₀.pairing v v ≠ 1) := by
  have hinst : instMod = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  subst hinst
  haveI := instFree
  haveI := instFinite
  have hu : IsOrthonormal pairing u := ⟨hnorm, horth⟩
  have hcore : ∀ w ∈ unitPerp pairing u, pairing w w ≠ 1 :=
    fun w hw => hfree w (mem_unitPerp.mp hw)
  have hunimod : Function.Bijective (pairing.restrict (unitPerp pairing u)) :=
    restrict_unitPerp_bijective pairing hu hsymm hbij
  have hsplit : Module.finrank ℤ (unitPerp pairing u) + k = n := by
    have h := NormOneSplitting.finrank_core_add
      (B := pairing)
      { rank := k, units := u, orthonormal := hu, core_normOneFree := hcore,
        core_unimodular := hunimod }
    rw [hrank] at h
    exact h
  refine ⟨{ carrier := ModuleCat.of ℤ ↥(unitPerp pairing u)
            pairing := pairing.restrict (unitPerp pairing u)
            symmetric := hsymm.restrict _
            positiveDefinite := ?_
            unimodular := hunimod
            rank := by
              show Module.finrank ℤ ↥(unitPerp pairing u) = n - k
              omega },
    (unitPerp pairing u).subtype.toAddMonoidHom, fun v w => rfl, ?_, ?_⟩
  · intro v hv
    exact hpd (v : X) fun h => hv (Subtype.ext h)
  · intro y hy
    exact ⟨⟨y, mem_unitPerp.mpr hy⟩, rfl⟩
  · intro v
    exact hcore (v : X) v.2

end Lattice

namespace OddUnimodularLattice15

/-- **The frame complement of a rank-15 host is a rank-`(15 - k)` lattice.**

`SRG266.Lattice.exists_pdCore_of_module` against the bundled carrier of a
`SRG266.OddUnimodularLattice15`.  The three clauses say that the inclusion
preserves the pairing, that its image is *exactly* the set of vectors
orthogonal to the frame, and that the complement carries no norm-one vector —
which are the three things `SRG266.Lattice.IsHostCoreModel` and
`SRG266.RootedCorankFourClassification` need between them. -/
theorem exists_frameCore (L : OddUnimodularLattice15) {k : ℕ} (u : Fin k → L.carrier)
    (hnorm : ∀ i, L.pairing (u i) (u i) = 1)
    (horth : ∀ i j, i ≠ j → L.pairing (u i) (u j) = 0)
    (hfree : ∀ w : L.carrier, (∀ i, L.pairing (u i) w = 0) → L.pairing w w ≠ 1) :
    ∃ (L₀ : PDUnimodularLattice (15 - k)) (ι : L₀.carrier →+ L.carrier),
      (∀ v w : L₀.carrier, L.pairing (ι v) (ι w) = L₀.pairing v w) ∧
      (∀ y : L.carrier, (∀ i, L.pairing (u i) y = 0) → ∃ z : L₀.carrier, ι z = y) ∧
      (∀ v : L₀.carrier, L₀.pairing v v ≠ 1) :=
  Lattice.exists_pdCore_of_module _ L.pairing L.moduleFree L.moduleFinite
    L.symmetric L.positiveDefinite L.unimodular L.rank u hnorm horth hfree

end OddUnimodularLattice15

namespace Lattice

/-- **A matrix model of the frame complement is a host core model.**

The composite of the classifying isometry with the inclusion of the complement
is the pairing-preserving map `SRG266.Lattice.IsHostCoreModel` asks for, and its
cover clause is exactly surjectivity of the isometry composed with the image
description of the inclusion. -/
theorem isHostCoreModel_of_isMatrixModel {L : OddUnimodularLattice15} {k n₀ m : ℕ}
    {u : Fin k → L.carrier} {L₀ : PDUnimodularLattice n₀}
    (ι : L₀.carrier →+ L.carrier)
    (hpair : ∀ v w : L₀.carrier, L.pairing (ι v) (ι w) = L₀.pairing v w)
    (hcover : ∀ y : L.carrier, (∀ i, L.pairing (u i) y = 0) → ∃ z : L₀.carrier, ι z = y)
    {A : Matrix (Fin m) (Fin m) ℤ} (hmodel : IsMatrixModel L₀ A) :
    IsHostCoreModel L u A := by
  obtain ⟨f, hf⟩ := hmodel
  refine ⟨(toZLinearMap ι).comp (f : (Fin m → ℤ) →ₗ[ℤ] L₀.carrier), ?_, ?_⟩
  · intro v w
    simpa [hpair] using hf v w
  · intro y hy
    obtain ⟨z, hz⟩ := hcover y hy
    exact ⟨f.symm z, by simp [hz]⟩

end Lattice

end SRG266
