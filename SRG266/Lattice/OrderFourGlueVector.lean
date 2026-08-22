/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.OrderFourGlueArithmetic

/-!
# The order-four full-rank `A15` glue case

This file removes the final full-rank glue-vector input from the theta-eutaxy
route.  If `R = A15` is embedded with full rank in a unimodular lattice `L`,
then `[L : R] = 4`.  For every quotient class choose a representative `x` and
root coordinates `g` with `4x = f(g)`.  Reduction modulo four sends the class
to the `A15` Cartan kernel.

The first coordinate of `g mod 4` defines an injection

`L / R -> ZMod 4`.

Both sides have four elements, so the map is onto.  A preimage of `1` has
numerator congruent to `(1,2,...,15)` modulo four; subtracting a root vector
gives the normalized glue relation required by `A15GlueTransport`.
-/

namespace SRG266
namespace Lattice

/-! ## Mod-four normalization lemmas -/

/-- A fourth multiple in an isometric root embedding has numerator in the
mod-four Cartan kernel. -/
theorem modFourVector_mem_cartanKernel_of_four_eq
    {n : ℕ} (L : PDUnimodularLattice n)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (f : (Fin n → ℤ) →ₗ[ℤ] L.carrier)
    (hpair : ∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' A v w)
    (x : L.carrier) (g : Fin n → ℤ) (hg : (4 : ℤ) • x = f g) :
    InModFourCartanKernel A (modFourVector g) := by
  intro j
  let e : Fin n → ℤ := Pi.single j 1
  have hform : Matrix.toBilin' A g e = ∑ i, g i * A i j := by
    rw [toBilin'_eq_vecMul_dotProduct, dotProduct_single, mul_one]
    rfl
  have hdiv : (4 : ℤ) ∣ ∑ i, g i * A i j := by
    refine ⟨L.pairing x (f e), ?_⟩
    calc
      ∑ i, g i * A i j = Matrix.toBilin' A g e := hform.symm
      _ = L.pairing (f g) (f e) := (hpair g e).symm
      _ = L.pairing ((4 : ℤ) • x) (f e) := by rw [hg]
      _ = 4 * L.pairing x (f e) := by simp
  have hcast : ((∑ i, g i * A i j : ℤ) : ZMod 4) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr hdiv
  rw [Int.cast_sum] at hcast
  simpa only [modFourVector, Int.cast_mul] using hcast

/-- Equality modulo four gives an integral quarter-difference. -/
theorem exists_add_four_of_modFourVector_eq {n : ℕ} (g s : Fin n → ℤ)
    (h : modFourVector g = modFourVector s) :
    ∃ a : Fin n → ℤ, g = s + (4 : ℤ) • a := by
  have hdvd : ∀ i, (4 : ℤ) ∣ g i - s i := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (g i - s i) 4).mp
    have hi := congrFun h i
    change (g i : ZMod 4) = (s i : ZMod 4) at hi
    rw [Int.cast_sub, hi, sub_self]
  choose a ha using hdvd
  refine ⟨a, funext fun i => ?_⟩
  change g i = s i + 4 * a i
  have hi := ha i
  omega

/-- Subtracting the integral quarter-difference normalizes a glue relation. -/
theorem exists_normalized_quarterGlue_of_modFourVector_eq
    {n : ℕ} (L : PDUnimodularLattice n)
    (f : (Fin n → ℤ) →ₗ[ℤ] L.carrier)
    (x : L.carrier) (g s : Fin n → ℤ)
    (hg : (4 : ℤ) • x = f g)
    (hclass : modFourVector g = modFourVector s) :
    ∃ y : L.carrier, (4 : ℤ) • y = f s := by
  obtain ⟨a, rfl⟩ := exists_add_four_of_modFourVector_eq g s hclass
  refine ⟨x - f a, ?_⟩
  calc
    (4 : ℤ) • (x - f a) = (4 : ℤ) • x - (4 : ℤ) • f a := by rw [zsmul_sub]
    _ = f (s + (4 : ℤ) • a) - f ((4 : ℤ) • a) := by rw [hg, map_zsmul]
    _ = f s := by rw [map_add]; abel

theorem eq_zero_of_four_zsmul_eq_zero
    {n : ℕ} (L : PDUnimodularLattice n) {x : L.carrier}
    (h : (4 : ℤ) • x = 0) : x = 0 := by
  letI := L.moduleFree
  letI : IsAddTorsionFree L.carrier :=
    IsAddTorsionFree.of_isTorsionFree ℤ L.carrier
  exact
    (IsAddTorsionFree.zsmul_eq_zero_iff_right
      (by norm_num : (4 : ℤ) ≠ 0)).mp h

/-! ## Choosing quotient representatives -/

/-- A representative of an index-four quotient class together with root
coordinates for its fourth multiple. -/
structure IndexFourGlueWitness {X : Type*} [AddCommGroup X] {n : ℕ}
    (f : (Fin n → ℤ) →+ X) (q : X ⧸ f.range) where
  representative : X
  numerator : Fin n → ℤ
  mk_representative : QuotientAddGroup.mk' f.range representative = q
  four_representative : (4 : ℤ) • representative = f numerator

theorem nonempty_indexFourGlueWitness
    {X : Type*} [AddCommGroup X] {n : ℕ}
    (f : (Fin n → ℤ) →+ X)
    (hcard : Nat.card (X ⧸ f.range) = 4) (q : X ⧸ f.range) :
    Nonempty (IndexFourGlueWitness f q) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective f.range q
  have hfour : (4 : ℕ) • (QuotientAddGroup.mk' f.range x) = 0 := by
    simpa [hcard] using
      (card_nsmul_eq_zero' (x := QuotientAddGroup.mk' f.range x))
  have hmem : (4 : ℕ) • x ∈ f.range := by
    apply (QuotientAddGroup.eq_zero_iff ((4 : ℕ) • x)).mp
    simpa using hfour
  obtain ⟨g, hg⟩ := hmem
  exact ⟨x, g, rfl, by simpa only [ofNat_zsmul] using hg.symm⟩

/-- A fixed choice of the representative-and-numerator package above. -/
noncomputable def indexFourGlueWitness
    {X : Type*} [AddCommGroup X] {n : ℕ}
    (f : (Fin n → ℤ) →+ X)
    (hcard : Nat.card (X ⧸ f.range) = 4) (q : X ⧸ f.range) :
    IndexFourGlueWitness f q :=
  Classical.choice (nonempty_indexFourGlueWitness f hcard q)

/-- The first mod-four root coordinate of a chosen quotient representative. -/
noncomputable def indexFourCoeffMap
    {X : Type*} [AddCommGroup X]
    (f : (Fin 15 → ℤ) →+ X)
    (hcard : Nat.card (X ⧸ f.range) = 4) :
    (X ⧸ f.range) → ZMod 4 := fun q =>
  modFourVector (indexFourGlueWitness f hcard q).numerator 0

/-! ## The quotient injects into the cyclic Cartan kernel -/

theorem indexFourCoeffMap_injective
    (L : PDUnimodularLattice 15)
    (f : (Fin 15 → ℤ) →ₗ[ℤ] L.carrier)
    (hpair : ∀ v w, L.pairing (f v) (f w) =
      Matrix.toBilin' (gramA 15) v w)
    (hcard : Nat.card (L.carrier ⧸ f.toAddMonoidHom.range) = 4) :
    Function.Injective (indexFourCoeffMap f.toAddMonoidHom hcard) := by
  intro q₁ q₂ hcoeff
  let w₁ := indexFourGlueWitness f.toAddMonoidHom hcard q₁
  let w₂ := indexFourGlueWitness f.toAddMonoidHom hcard q₂
  have hk₁ : InModFourCartanKernel (gramA 15)
      (modFourVector w₁.numerator) :=
    modFourVector_mem_cartanKernel_of_four_eq L (gramA 15) f hpair
      w₁.representative w₁.numerator w₁.four_representative
  have hk₂ : InModFourCartanKernel (gramA 15)
      (modFourVector w₂.numerator) :=
    modFourVector_mem_cartanKernel_of_four_eq L (gramA 15) f hpair
      w₂.representative w₂.numerator w₂.four_representative
  have hzero : modFourVector w₁.numerator 0 = modFourVector w₂.numerator 0 := by
    change indexFourCoeffMap f.toAddMonoidHom hcard q₁ =
      indexFourCoeffMap f.toAddMonoidHom hcard q₂
    exact hcoeff
  have hclass : modFourVector w₁.numerator = modFourVector w₂.numerator :=
    a15_modFour_kernel_ext hk₁ hk₂ hzero
  obtain ⟨a, ha⟩ := exists_add_four_of_modFourVector_eq
    w₁.numerator w₂.numerator hclass
  have hkill : (4 : ℤ) •
      (w₁.representative - w₂.representative - f a) = 0 := by
    calc
      (4 : ℤ) • (w₁.representative - w₂.representative - f a) =
          (4 : ℤ) • w₁.representative -
            (4 : ℤ) • w₂.representative - (4 : ℤ) • f a := by
              rw [zsmul_sub, zsmul_sub]
      _ = f.toAddMonoidHom w₁.numerator - f.toAddMonoidHom w₂.numerator -
          (4 : ℤ) • f a := by
            rw [w₁.four_representative, w₂.four_representative]
      _ = 0 := by
        change f w₁.numerator - f w₂.numerator - (4 : ℤ) • f a = 0
        rw [← map_zsmul, ha, map_add]
        abel
  have hdiff : w₁.representative - w₂.representative = f a :=
    sub_eq_zero.mp (eq_zero_of_four_zsmul_eq_zero L hkill)
  calc
    q₁ = QuotientAddGroup.mk' f.toAddMonoidHom.range w₁.representative :=
      w₁.mk_representative.symm
    _ = QuotientAddGroup.mk' f.toAddMonoidHom.range w₂.representative := by
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      exact ⟨a, hdiff.symm⟩
    _ = q₂ := w₂.mk_representative

/-! ## The normalized `A15` glue vector -/

theorem HasFullRankRootType.exists_a15_embedding_index_four_with_pairing
    (L : PDUnimodularLattice 15) (h : HasFullRankRootType L [.A 15]) :
    ∃ f : (Fin 15 → ℤ) →ₗ[ℤ] L.carrier,
      Function.Injective f ∧
        (∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' (gramA 15) v w) ∧
        Nat.card (L.carrier ⧸ f.toAddMonoidHom.range) = 4 := by
  obtain ⟨us, hperm, hrank, hroot⟩ := h
  have hus : us = [.A 15] := hperm.eq_singleton
  subst us
  obtain ⟨f, hf, hpair, hindex⟩ :=
    hroot.exists_image_index L [.A 15] rfl
  have hdet : (adeGram [.A 15]).2.det = 16 := by
    calc
      (adeGram [.A 15]).2.det = (ADEType.A 15).gram.det :=
        congrArg Matrix.det (adeGram_singleton (.A 15))
      _ = 16 := by rw [det_gram_a15]; rfl
  rw [hdet] at hindex
  norm_num at hindex
  have hcard : Nat.card (L.carrier ⧸ f.toAddMonoidHom.range) = 4 :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (by simpa using hindex)
  refine ⟨f, hf, ?_, hcard⟩
  intro v w
  change L.pairing (f v) (f w) =
    Matrix.toBilin' (ADEType.A 15).gram v w
  exact hpair v w

/-- The full `A15` discriminant argument.  No classification input is used:
the index-four quotient and the mod-four Cartan kernel both have four
elements, forcing the standard order-four glue class to occur. -/
theorem a15NormalizedGlueVector : A15NormalizedGlueVectorInput := by
  intro L _hfree hroot
  obtain ⟨f, hf, hpair, hcard⟩ :=
    hroot.exists_a15_embedding_index_four_with_pairing L
  let Q := L.carrier ⧸ f.toAddMonoidHom.range
  let coeff : Q → ZMod 4 := indexFourCoeffMap f.toAddMonoidHom hcard
  have hinj : Function.Injective coeff :=
    indexFourCoeffMap_injective L f hpair hcard
  letI : Finite Q := Nat.finite_of_card_ne_zero (by
    simp [Q, hcard])
  have hbij : Function.Bijective coeff :=
    hinj.bijective_of_nat_card_le (by
      simp [Q, hcard])
  obtain ⟨q, hq⟩ := hbij.2 (1 : ZMod 4)
  let w := indexFourGlueWitness f.toAddMonoidHom hcard q
  have hcoeff : modFourVector w.numerator 0 = 1 := by
    change coeff q = 1
    exact hq
  have hkernel : InModFourCartanKernel (gramA 15)
      (modFourVector w.numerator) :=
    modFourVector_mem_cartanKernel_of_four_eq L (gramA 15) f hpair
      w.representative w.numerator w.four_representative
  have hclass : modFourVector w.numerator =
      modFourVector a15GlueNumerator := by
    calc
      modFourVector w.numerator =
          a15ModFourPattern (modFourVector w.numerator 0) :=
        a15_modFour_kernel_eq_pattern _ hkernel
      _ = a15ModFourPattern 1 := by rw [hcoeff]
      _ = modFourVector a15GlueNumerator := a15ModFourPattern_one
  obtain ⟨y, hy⟩ := exists_normalized_quarterGlue_of_modFourVector_eq
    L f w.representative w.numerator a15GlueNumerator
      w.four_representative hclass
  exact ⟨f, y, hpair, hy⟩

/-- The theta-eutaxy/ADE structural theorem implies the corank-four
classification boundary. -/
theorem rootedCorankFourClassification_of_thetaEutaxy
    (hTheta : ThetaEutacticADEDecompositionInput) :
    RootedCorankFourClassification :=
  rootedCorankFourClassification_of_thetaEutaxy_glueVectors hTheta
    d12NormalizedGlueVector e7e7NormalizedGlueVector a15NormalizedGlueVector

end Lattice
end SRG266
