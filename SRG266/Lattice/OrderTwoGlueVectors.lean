/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.OrderTwoGlueArithmetic

/-!
# The order-two full-rank glue cases

This module discharges the residual normalized glue-vector inputs for `D12`
and `E7 + E7`.  Both root lattices have index two in the ambient unimodular
lattice.  A nonzero quotient class therefore has a representative `x` with
`2x` in the root lattice.  The remaining mod-two Cartan arithmetic identifies
its discriminant class.
-/

namespace SRG266
namespace Lattice

/-- A subgroup of index two supplies a nontrivial representative whose double
lies in the subgroup. -/
theorem exists_not_mem_and_double_mem_of_quotient_card_two
    {X : Type*} [AddCommGroup X] (f : (Fin n → ℤ) →+ X)
    (hcard : Nat.card (X ⧸ f.range) = 2) :
    ∃ (x : X) (g : Fin n → ℤ), x ∉ f.range ∧ (2 : ℤ) • x = f g := by
  let Q := X ⧸ f.range
  have hex : ∃ q : Q, q ≠ 0 := by
    by_contra h
    push Not at h
    have hsub : Subsingleton Q := ⟨fun a b => (h a).trans (h b).symm⟩
    have hone : Nat.card Q = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩
    have htwo := hcard
    change Nat.card Q = 2 at htwo
    omega
  obtain ⟨q, hq⟩ := hex
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective f.range q
  have htwo : (2 : ℕ) • (QuotientAddGroup.mk' f.range x) = 0 := by
    simpa [hcard] using
      (card_nsmul_eq_zero' (x := QuotientAddGroup.mk' f.range x))
  have hmem : (2 : ℕ) • x ∈ f.range := by
    apply (QuotientAddGroup.eq_zero_iff ((2 : ℕ) • x)).mp
    simpa using htwo
  obtain ⟨g, hg⟩ := hmem
  refine ⟨x, g, ?_, ?_⟩
  · intro hx
    exact hq ((QuotientAddGroup.eq_zero_iff x).mpr hx)
  · simpa only [ofNat_zsmul] using hg.symm

/-! ## From an abstract index-two embedding to its mod-two class -/

/-- If `2x = f(g)` for an isometric root embedding, then `g` lies in the
mod-two Cartan kernel. -/
theorem modTwoVector_mem_cartanKernel_of_double_eq
    {n : ℕ} (L : PDUnimodularLattice n)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (f : (Fin n → ℤ) →ₗ[ℤ] L.carrier)
    (hpair : ∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' A v w)
    (x : L.carrier) (g : Fin n → ℤ) (hg : (2 : ℤ) • x = f g) :
    InModTwoCartanKernel A (modTwoVector g) := by
  intro j
  let e : Fin n → ℤ := Pi.single j 1
  have hform : Matrix.toBilin' A g e = ∑ i, g i * A i j := by
    rw [toBilin'_eq_vecMul_dotProduct, dotProduct_single, mul_one]
    rfl
  have heven : (2 : ℤ) ∣ ∑ i, g i * A i j := by
    refine ⟨L.pairing x (f e), ?_⟩
    calc
      ∑ i, g i * A i j = Matrix.toBilin' A g e := hform.symm
      _ = L.pairing (f g) (f e) := (hpair g e).symm
      _ = L.pairing ((2 : ℤ) • x) (f e) := by rw [hg]
      _ = 2 * L.pairing x (f e) := by simp
  have hcast : ((∑ i, g i * A i j : ℤ) : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr heven
  rw [Int.cast_sum] at hcast
  simpa only [modTwoVector, Int.cast_mul] using hcast

/-- Equality modulo two gives an integral half-difference. -/
theorem exists_add_double_of_modTwoVector_eq {n : ℕ} (g s : Fin n → ℤ)
    (h : modTwoVector g = modTwoVector s) :
    ∃ a : Fin n → ℤ, g = s + (2 : ℤ) • a := by
  have hdvd : ∀ i, (2 : ℤ) ∣ g i - s i := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (g i - s i) 2).mp
    have hi := congrFun h i
    change (g i : ZMod 2) = (s i : ZMod 2) at hi
    rw [Int.cast_sub, hi, sub_self]
  choose a ha using hdvd
  refine ⟨a, funext fun i => ?_⟩
  change g i = s i + 2 * a i
  have hi := ha i
  omega

/-- Removing the integral half-difference normalizes a glue relation. -/
theorem exists_normalized_halfGlue_of_modTwoVector_eq
    {n : ℕ} (L : PDUnimodularLattice n)
    (f : (Fin n → ℤ) →ₗ[ℤ] L.carrier)
    (x : L.carrier) (g s : Fin n → ℤ)
    (hg : (2 : ℤ) • x = f g)
    (hclass : modTwoVector g = modTwoVector s) :
    ∃ y : L.carrier, (2 : ℤ) • y = f s := by
  obtain ⟨a, rfl⟩ := exists_add_double_of_modTwoVector_eq g s hclass
  refine ⟨x - f a, ?_⟩
  calc
    (2 : ℤ) • (x - f a) = (2 : ℤ) • x - (2 : ℤ) • f a := by rw [zsmul_sub]
    _ = f (s + (2 : ℤ) • a) - f ((2 : ℤ) • a) := by rw [hg, map_zsmul]
    _ = f s := by rw [map_add]; abel

/-- A nonzero additive multiple cannot annihilate a vector in a free integer
module. -/
theorem eq_zero_of_two_zsmul_eq_zero
    {n : ℕ} (L : PDUnimodularLattice n) {x : L.carrier}
    (h : (2 : ℤ) • x = 0) : x = 0 := by
  letI := L.moduleFree
  letI : IsAddTorsionFree L.carrier :=
    IsAddTorsionFree.of_isTorsionFree ℤ L.carrier
  exact
    (IsAddTorsionFree.zsmul_eq_zero_iff_right
      (by norm_num : (2 : ℤ) ≠ 0)).mp h

theorem not_zero_modTwoVector_of_not_mem_range
    {n : ℕ} (L : PDUnimodularLattice n)
    (f : (Fin n → ℤ) →ₗ[ℤ] L.carrier)
    (x : L.carrier) (g : Fin n → ℤ)
    (hx : x ∉ f.toAddMonoidHom.range) (hg : (2 : ℤ) • x = f g) :
    modTwoVector g ≠ 0 := by
  intro hzero
  obtain ⟨a, ha⟩ := exists_add_double_of_modTwoVector_eq g 0 hzero
  have hkill : (2 : ℤ) • (x - f a) = 0 := by
    calc
      (2 : ℤ) • (x - f a) = (2 : ℤ) • x - (2 : ℤ) • f a := by rw [zsmul_sub]
      _ = f (0 + (2 : ℤ) • a) - f ((2 : ℤ) • a) := by rw [hg, ha, map_zsmul]
      _ = 0 := by simp
  have hxa : x = f a := sub_eq_zero.mp (eq_zero_of_two_zsmul_eq_zero L hkill)
  exact hx ⟨a, hxa.symm⟩

/-! ## Full-rank embeddings with their index and form -/

theorem HasFullRankRootType.exists_d12_embedding_index_two
    (L : PDUnimodularLattice 12) (h : HasFullRankRootType L [.D 12]) :
    ∃ f : (Fin 12 → ℤ) →ₗ[ℤ] L.carrier,
      Function.Injective f ∧
        (∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' (gramD 12) v w) ∧
        Nat.card (L.carrier ⧸ f.toAddMonoidHom.range) = 2 := by
  obtain ⟨us, hperm, hrank, hroot⟩ := h
  have hus : us = [.D 12] := hperm.eq_singleton
  subst us
  obtain ⟨f, hf, hpair, hindex⟩ :=
    hroot.exists_image_index L [.D 12] rfl
  have hdet : (adeGram [.D 12]).2.det = 4 := by
    calc
      (adeGram [.D 12]).2.det = (ADEType.D 12).gram.det :=
        congrArg Matrix.det (adeGram_singleton (.D 12))
      _ = 4 := by rw [det_gram_d12]; rfl
  rw [hdet] at hindex
  norm_num at hindex
  have hcard : Nat.card (L.carrier ⧸ f.toAddMonoidHom.range) = 2 :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (by simpa using hindex)
  refine ⟨f, hf, ?_, hcard⟩
  intro v w
  change L.pairing (f v) (f w) =
    Matrix.toBilin' (ADEType.D 12).gram v w
  exact hpair v w

theorem HasFullRankRootType.exists_e7e7_embedding_index_two
    (L : PDUnimodularLattice 14) (h : HasFullRankRootType L [.E7, .E7]) :
    ∃ f : (Fin 14 → ℤ) →ₗ[ℤ] L.carrier,
      Function.Injective f ∧
        (∀ v w, L.pairing (f v) (f w) =
          Matrix.toBilin' (adeGram [.E7, .E7]).2 v w) ∧
        Nat.card (L.carrier ⧸ f.toAddMonoidHom.range) = 2 := by
  obtain ⟨us, hperm, hrank, hroot⟩ := h
  have hlen : us.length = 2 := by simpa using hperm.length_eq
  have hall : ∀ t ∈ us, t = ADEType.E7 := by
    intro t ht
    have ht' : t ∈ [.E7, .E7] := hperm.mem_iff.mp ht
    simpa using ht'
  have hus : us = [.E7, .E7] := by
    have hrep : us = List.replicate us.length ADEType.E7 :=
      List.eq_replicate_length.mpr hall
    simpa [hlen] using hrep
  subst us
  obtain ⟨f, hf, hpair, hindex⟩ :=
    hroot.exists_image_index L [.E7, .E7] rfl
  rw [det_adeGram_e7_e7] at hindex
  norm_num at hindex
  have hcard : Nat.card (L.carrier ⧸ f.toAddMonoidHom.range) = 2 :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (by simpa using hindex)
  exact ⟨f, hf, hpair, hcard⟩

/-! ## Norm tests for the inadmissible residue classes -/

theorem four_mul_pairing_eq_root_norm_of_double_eq
    {n : ℕ} (L : PDUnimodularLattice n)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (f : (Fin n → ℤ) →ₗ[ℤ] L.carrier)
    (hpair : ∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' A v w)
    (y : L.carrier) (s : Fin n → ℤ) (hy : (2 : ℤ) • y = f s) :
    4 * L.pairing y y = Matrix.toBilin' A s s := by
  calc
    4 * L.pairing y y = L.pairing ((2 : ℤ) • y) ((2 : ℤ) • y) := by
      rw [map_zsmul, map_zsmul, LinearMap.smul_apply]
      simp only [zsmul_eq_mul, Int.cast_id]
      ring
    _ = L.pairing (f s) (f s) := by rw [hy]
    _ = Matrix.toBilin' A s s := hpair s s

theorem d12VectorClassNumerator_norm :
    Matrix.toBilin' (gramD 12) d12VectorClassNumerator
      d12VectorClassNumerator = 4 := by
  decide +kernel

theorem e7e7LeftGlueNumerator_norm :
    Matrix.toBilin' (adeGram [.E7, .E7]).2 e7e7LeftGlueNumerator
      e7e7LeftGlueNumerator = 14 := by
  decide +kernel

theorem e7e7RightGlueNumerator_norm :
    Matrix.toBilin' (adeGram [.E7, .E7]).2 e7e7RightGlueNumerator
      e7e7RightGlueNumerator = 14 := by
  decide +kernel

/-! ## The `D12` diagram automorphism -/

/-- The terminal-node swap on the `D12` simple-root basis. -/
def d12DiagramSwapMatrix : Matrix (Fin 12) (Fin 12) ℤ := fun i j =>
  if i = 10 then if j = 11 then 1 else 0
  else if i = 11 then if j = 10 then 1 else 0
  else if i = j then 1 else 0

theorem d12DiagramSwap_gram :
    d12DiagramSwapMatrix.transpose * gramD 12 * d12DiagramSwapMatrix =
      gramD 12 := by
  decide +kernel

theorem d12DiagramSwap_glueNumerator :
    d12DiagramSwapMatrix.mulVec d12GlueNumerator = d12OtherGlueNumerator := by
  decide +kernel

/-! ## Discharging the two order-two glue inputs -/

/-- The full `D12` discriminant argument.  The zero class contradicts the
choice of a non-root coset, the vector class would create a norm-one vector,
and the two spinor classes are exchanged by the terminal-node automorphism. -/
theorem d12NormalizedGlueVector : D12NormalizedGlueVectorInput := by
  intro L hfree hroot
  obtain ⟨f, hf, hpair, hcard⟩ := hroot.exists_d12_embedding_index_two L
  obtain ⟨x, g, hx, hg⟩ :=
    exists_not_mem_and_double_mem_of_quotient_card_two f.toAddMonoidHom hcard
  have hkernel := modTwoVector_mem_cartanKernel_of_double_eq
    L (gramD 12) f hpair x g hg
  have hnz := not_zero_modTwoVector_of_not_mem_range L f x g hx hg
  rcases d12_modTwo_kernel_cases (modTwoVector g) hkernel with
      hzero | hspin | hother | hvector
  · exact False.elim (hnz hzero)
  · obtain ⟨y, hy⟩ := exists_normalized_halfGlue_of_modTwoVector_eq
      L f x g d12GlueNumerator hg hspin
    exact ⟨f, y, hpair, hy⟩
  · obtain ⟨y, hy⟩ := exists_normalized_halfGlue_of_modTwoVector_eq
      L f x g d12OtherGlueNumerator hg hother
    let f' : (Fin 12 → ℤ) →ₗ[ℤ] L.carrier :=
      f.comp d12DiagramSwapMatrix.mulVecLin
    have hpair' : ∀ v w, L.pairing (f' v) (f' w) =
        Matrix.toBilin' (gramD 12) v w := by
      intro v w
      calc
        L.pairing (f' v) (f' w) =
            Matrix.toBilin' (gramD 12)
              (d12DiagramSwapMatrix.mulVec v)
              (d12DiagramSwapMatrix.mulVec w) := hpair _ _
        _ = Matrix.toBilin' (gramD 12) v w :=
          toBilin'_mulVec_of_transpose_mul_mul
            (gramD 12) (gramD 12) d12DiagramSwapMatrix
              d12DiagramSwap_gram v w
    have hy' : (2 : ℤ) • y = f' d12GlueNumerator := by
      calc
        (2 : ℤ) • y = f d12OtherGlueNumerator := hy
        _ = f (d12DiagramSwapMatrix.mulVec d12GlueNumerator) := by
          rw [d12DiagramSwap_glueNumerator]
        _ = f' d12GlueNumerator := rfl
    exact ⟨f', y, hpair', hy'⟩
  · obtain ⟨y, hy⟩ := exists_normalized_halfGlue_of_modTwoVector_eq
      L f x g d12VectorClassNumerator hg hvector
    have hnorm4 := four_mul_pairing_eq_root_norm_of_double_eq
      L (gramD 12) f hpair y d12VectorClassNumerator hy
    rw [d12VectorClassNumerator_norm] at hnorm4
    have hnorm : L.pairing y y = 1 := by omega
    exact False.elim (hfree y hnorm)

/-- The full `(E7 + E7)` discriminant argument.  A one-factor class would
have numerator norm 14, impossible after division by four in an integral
lattice; hence the nonzero quotient class is the diagonal glue. -/
theorem e7e7NormalizedGlueVector : E7E7NormalizedGlueVectorInput := by
  intro L _hfree hroot
  obtain ⟨f, hf, hpair, hcard⟩ := hroot.exists_e7e7_embedding_index_two L
  obtain ⟨x, g, hx, hg⟩ :=
    exists_not_mem_and_double_mem_of_quotient_card_two f.toAddMonoidHom hcard
  have hkernel := modTwoVector_mem_cartanKernel_of_double_eq
    L (adeGram [.E7, .E7]).2 f hpair x g hg
  have hnz := not_zero_modTwoVector_of_not_mem_range L f x g hx hg
  rcases e7e7_modTwo_kernel_cases (modTwoVector g) hkernel with
      hzero | hleft | hright | hdiag
  · exact False.elim (hnz hzero)
  · obtain ⟨y, hy⟩ := exists_normalized_halfGlue_of_modTwoVector_eq
      L f x g e7e7LeftGlueNumerator hg hleft
    have hnorm14 := four_mul_pairing_eq_root_norm_of_double_eq
      L (adeGram [.E7, .E7]).2 f hpair y e7e7LeftGlueNumerator hy
    have hnorm14' : 4 * L.pairing y y = 14 :=
      hnorm14.trans e7e7LeftGlueNumerator_norm
    omega
  · obtain ⟨y, hy⟩ := exists_normalized_halfGlue_of_modTwoVector_eq
      L f x g e7e7RightGlueNumerator hg hright
    have hnorm14 := four_mul_pairing_eq_root_norm_of_double_eq
      L (adeGram [.E7, .E7]).2 f hpair y e7e7RightGlueNumerator hy
    have hnorm14' : 4 * L.pairing y y = 14 :=
      hnorm14.trans e7e7RightGlueNumerator_norm
    omega
  · obtain ⟨y, hy⟩ := exists_normalized_halfGlue_of_modTwoVector_eq
      L f x g e7e7GlueNumerator hg hdiag
    exact ⟨f, y, hpair, hy⟩

/-- After the order-two arithmetic, the minimized theta-eutaxy route has only
the `A15` order-four divisibility statement left. -/
theorem rootedCorankFourClassification_of_thetaEutaxy_a15GlueVector
    (hTheta : ThetaEutacticADEDecompositionInput)
    (hA15 : A15NormalizedGlueVectorInput) :
    RootedCorankFourClassification :=
  rootedCorankFourClassification_of_thetaEutaxy_glueVectors hTheta
    d12NormalizedGlueVector e7e7NormalizedGlueVector hA15

end Lattice
end SRG266
