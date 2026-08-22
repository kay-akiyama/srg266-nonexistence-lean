/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Transport
import SRG266.Lattice.FrameCore

/-!
# Transport of a self-dual rational lattice in arbitrary rank

`SRG266.Lattice.exists_oddUnimodularLattice15` transports a self-dual lattice
in a rational quadratic space to the bundled rank-fifteen odd lattice used by
the Yang--Yoshino construction.  The even-neighbour argument needs the same
basis transport in rank twenty four, without an oddness field.

The theorem below is that rank-generic counterpart.  It returns a linear
*equivalence*, rather than only an injective map, because the root partition
of the rational presentation must be transported without losing
multiplicities.
-/

namespace SRG266.Lattice

open Module
open scoped Matrix

variable {X : Type*} [AddCommGroup X] [Module ℚ X]

/-- A positive-definite self-dual lattice of rank `n` in a rational quadratic
space transports to `PDUnimodularLattice n`. -/
theorem exists_pdUnimodularLattice {n : ℕ}
    {F : LinearMap.BilinForm ℚ X} (hsymm : F.IsSymm)
    (hpd : ∀ v : X, v ≠ 0 → 0 < F v v) (hrank : Module.finrank ℚ X = n)
    {H : Submodule ℤ X} (hlat : IsLattice ℚ H)
    (hself : F.dualSubmodule H = H) :
    ∃ (L : PDUnimodularLattice n) (e : H ≃ₗ[ℤ] L.carrier),
      ∀ u v : H, ((L.pairing (e u) (e v) : ℤ) : ℚ) = F (u : X) (v : X) := by
  classical
  have hnd : F.Nondegenerate := nondegenerate_of_posDef hsymm hpd
  obtain ⟨d, b, hHspan⟩ := exists_basis_of_isLattice hlat
  have hdn : d = n := by
    have hcard := Module.finrank_eq_card_basis b
    rw [hrank, Fintype.card_fin] at hcard
    exact hcard.symm
  subst d
  subst hHspan
  have hbmem : ∀ i, b i ∈ Submodule.span ℤ (Set.range (b : Fin n → X)) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  have hintegral : ∀ i j, F (b i) (b j) ∈ (1 : Submodule ℤ ℚ) := by
    intro i j
    exact (le_of_eq hself.symm) (hbmem i) _ (hbmem j)
  set A : Matrix (Fin n) (Fin n) ℤ := fun i j => (F (b i) (b j)).num with hAdef
  have hA : ∀ i j, ((A i j : ℤ) : ℚ) = F (b i) (b j) := by
    intro i j
    obtain ⟨k, hk⟩ := mem_one_iff.mp (hintegral i j)
    rw [hAdef]
    simp only [← hk, Rat.num_intCast]
  have hli : LinearIndependent ℤ (b : Fin n → X) :=
    (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).mpr b.linearIndependent
  set bZ : Basis (Fin n) ℤ (Submodule.span ℤ (Set.range (b : Fin n → X))) :=
    Basis.span hli with hbZ
  have hbZcoe : ∀ i,
      ((bZ i : Submodule.span ℤ (Set.range (b : Fin n → X))) : X) = b i := by
    intro i
    rw [hbZ, Basis.span_apply]
  have hcoe : ∀ v : Fin n → ℤ,
      ((bZ.equivFun.symm v : Submodule.span ℤ (Set.range (b : Fin n → X))) : X) =
        coordSum (b : Fin n → X) v := by
    intro v
    rw [Basis.equivFun_symm_apply, coordSum_eq_zsmul_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [hbZcoe]
  have hsymmSpan : ∀ u : Submodule.span ℤ (Set.range (b : Fin n → X)),
      coordSum (b : Fin n → X) (bZ.equivFun u) = (u : X) := by
    intro u
    rw [← hcoe, LinearEquiv.symm_apply_apply]
  have hAsymm : A.IsSymm := by
    ext i j
    have h1 := hA i j
    have h2 := hA j i
    have : ((A j i : ℤ) : ℚ) = ((A i j : ℤ) : ℚ) := by
      rw [h1, h2, hsymm.eq (b j) (b i)]
    exact_mod_cast this
  have hApd : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < Matrix.toBilin' A v v := by
    intro v hv
    have hne : coordSum (b : Fin n → X) v ≠ 0 := fun h =>
      hv (coordSum_eq_zero b.linearIndependent h)
    have hpos := hpd _ hne
    rw [← toBilin'_coordSum (F := F) b A hA v v] at hpos
    exact_mod_cast hpos
  have hAbij : Function.Bijective (Matrix.toBilin' A) := by
    constructor
    · intro v w hvw
      have hzero : Matrix.toBilin' A (v - w) (v - w) = 0 := by
        have h1 : Matrix.toBilin' A (v - w) = 0 := by
          rw [map_sub, hvw, sub_self]
        rw [h1]
        rfl
      by_contra hne
      have hvw0 : v - w ≠ 0 := sub_ne_zero_of_ne hne
      have := hApd (v - w) hvw0
      rw [hzero] at this
      exact lt_irrefl 0 this
    · intro psi
      set c : Fin n → ℤ := fun i => psi (Pi.single i 1) with hc
      set dual : Fin n → X := fun i => F.dualBasis hnd b i with hdual
      have hdualspan : Submodule.span ℤ (Set.range dual) =
          Submodule.span ℤ (Set.range (b : Fin n → X)) := by
        rw [hdual, ← LinearMap.BilinForm.dualSubmodule_span_of_basis F hnd b]
        exact hself
      have hzmem : coordSum dual c ∈
          Submodule.span ℤ (Set.range (b : Fin n → X)) := by
        rw [← hdualspan]
        exact coordSum_mem_span dual c
      set v : Fin n → ℤ := bZ.equivFun ⟨coordSum dual c, hzmem⟩ with hv
      have hvcoord : coordSum (b : Fin n → X) v = coordSum dual c :=
        hsymmSpan ⟨coordSum dual c, hzmem⟩
      refine ⟨v, ?_⟩
      refine LinearMap.ext fun w => ?_
      have hzb : ∀ j, F (coordSum dual c) (b j) = (c j : ℚ) := by
        intro j
        rw [show coordSum dual c = ∑ i, (c i : ℚ) • dual i from rfl, map_sum,
          LinearMap.sum_apply]
        rw [Finset.sum_eq_single j]
        · rw [map_smul, LinearMap.smul_apply, hdual, smul_eq_mul,
            LinearMap.BilinForm.apply_dualBasis_left hnd b j j, if_pos rfl, mul_one]
        · intro i _ hij
          rw [map_smul, LinearMap.smul_apply, hdual, smul_eq_mul,
            LinearMap.BilinForm.apply_dualBasis_left hnd b i j,
            if_neg (Ne.symm hij), mul_zero]
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      have hsingle : ∀ (j : Fin n) (a : ℤ),
          (Pi.single j a : Fin n → ℤ) = a • (Pi.single j 1 : Fin n → ℤ) := by
        intro j a
        funext i
        by_cases h : i = j <;> simp [h]
      have hpsiw : psi w = ∑ j, w j * c j := by
        have hw : w = ∑ j, w j • (Pi.single j 1 : Fin n → ℤ) := by
          conv_lhs => rw [← Finset.univ_sum_single w]
          exact Finset.sum_congr rfl fun j _ => hsingle j (w j)
        conv_lhs => rw [hw]
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, hc]
      have hexp : F (coordSum dual c) (coordSum (b : Fin n → X) w) =
          ∑ j, (w j : ℚ) * (c j : ℚ) := by
        rw [show coordSum (b : Fin n → X) w =
          ∑ j, (w j : ℚ) • b j from rfl, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_eq_mul, hzb j]
      have hlhs : ((Matrix.toBilin' A v w : ℤ) : ℚ) =
          ((∑ j, w j * c j : ℤ) : ℚ) := by
        rw [toBilin'_coordSum (F := F) b A hA, hvcoord, hexp]
        push_cast
        rfl
      have : Matrix.toBilin' A v w = ∑ j, w j * c j := by
        exact_mod_cast hlhs
      rw [this, hpsiw]
  let L : PDUnimodularLattice n :=
    { carrier := ModuleCat.of ℤ (Fin n → ℤ)
      pairing := Matrix.toBilin' A
      symmetric := toBilin'_isSymm A hAsymm
      positiveDefinite := hApd
      unimodular := hAbij
      rank := Module.finrank_fin_fun ℤ }
  refine ⟨L, bZ.equivFun, ?_⟩
  intro u v
  show ((Matrix.toBilin' A (bZ.equivFun u) (bZ.equivFun v) : ℤ) : ℚ) =
    F (u : X) (v : X)
  rw [toBilin'_coordSum (F := F) b A hA, hsymmSpan u, hsymmSpan v]

end SRG266.Lattice
