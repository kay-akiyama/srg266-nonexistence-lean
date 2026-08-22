/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Glue
import SRG266.Lattice.HostBuilder

/-!
# Basis transport: a self-dual lattice becomes a bundled rank-15 host

`SRG266.OddUnimodularLattice15` bundles its carrier as an object of
`ModuleCat ℤ` in universe `0`; the glue
lattice of `SRG266/Lattice/Glue.lean` lives inside a rational quadratic space in
an arbitrary universe.  The bridge is a basis.

`SRG266.Lattice.exists_oddUnimodularLattice15` takes a positive-definite
symmetric rational form on a `15`-dimensional space together with a lattice `H`
that equals its own dual and contains a vector of odd norm, chooses a
`ℚ`-basis whose `ℤ`-span is `H` (`SRG266.Lattice.exists_basis_of_isLattice`),
transports the form to an integer `15 × 15` matrix, and
returns the resulting `OddUnimodularLattice15` together with an injective,
pairing-preserving embedding of `H`.

No `ULift` is needed: `SRG266.standardHost15` has the `Type 0` carrier
`Fin 15 → ℤ`.
-/

namespace SRG266.Lattice

open Module
open scoped Matrix

section TransportLemmas

variable {X : Type*} [AddCommGroup X] [Module ℚ X] {n : ℕ}

/-- The coordinate map of a family of vectors, on integer coordinate vectors. -/
def coordSum (b : Fin n → X) (v : Fin n → ℤ) : X := ∑ i, (v i : ℚ) • b i

theorem coordSum_eq_zsmul_sum (b : Fin n → X) (v : Fin n → ℤ) :
    coordSum b v = ∑ i, v i • b i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]

theorem coordSum_mem_span (b : Fin n → X) (v : Fin n → ℤ) :
    coordSum b v ∈ Submodule.span ℤ (Set.range b) := by
  rw [coordSum_eq_zsmul_sum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Integer coordinates against a `ℚ`-independent family are unique. -/
theorem coordSum_eq_zero {b : Fin n → X} (hli : LinearIndependent ℚ b) {v : Fin n → ℤ}
    (h : coordSum b v = 0) : v = 0 := by
  funext i
  have hz := Fintype.linearIndependent_iff.mp hli (fun i => (v i : ℚ)) h i
  exact_mod_cast hz

/-- **Transport of the form.**  If the integer matrix `A` records the pairings of
a family `b`, the matrix form on coordinate vectors is the original form on the
corresponding vectors. -/
theorem toBilin'_coordSum {F : LinearMap.BilinForm ℚ X} (b : Fin n → X)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : ∀ i j, ((A i j : ℤ) : ℚ) = F (b i) (b j))
    (v w : Fin n → ℤ) :
    ((Matrix.toBilin' A v w : ℤ) : ℚ) = F (coordSum b v) (coordSum b w) := by
  have hRHS : F (coordSum b v) (coordSum b w)
      = ∑ i, ∑ j, (v i : ℚ) * ((w j : ℚ) * F (b i) (b j)) := by
    rw [show coordSum b v = ∑ i, (v i : ℚ) • b i from rfl, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul,
      show coordSum b w = ∑ j, (w j : ℚ) • b j from rfl, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [hRHS, Matrix.toBilin'_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hA i j]
  ring

end TransportLemmas

section Transport

variable {X : Type*} [AddCommGroup X] [Module ℚ X]

/-- **Basis transport (YY §2.7).**  A positive-definite self-dual lattice of a
`15`-dimensional rational quadratic space, containing a vector of odd norm, is
an `SRG266.OddUnimodularLattice15`, and the lattice embeds in the bundled host
compatibly with the two pairings. -/
theorem exists_oddUnimodularLattice15 {F : LinearMap.BilinForm ℚ X} (hsymm : F.IsSymm)
    (hpd : ∀ v : X, v ≠ 0 → 0 < F v v) (hrank : Module.finrank ℚ X = 15)
    {H : Submodule ℤ X} (hlat : IsLattice ℚ H) (hself : F.dualSubmodule H = H)
    (hodd : ∃ z ∈ H, ∃ k : ℤ, ¬ Even k ∧ (k : ℚ) = F z z) :
    ∃ (L : OddUnimodularLattice15) (e : H →ₗ[ℤ] L.carrier),
      Function.Injective e ∧
        ∀ u v : H, ((L.pairing (e u) (e v) : ℤ) : ℚ) = F (u : X) (v : X) := by
  classical
  have hnd : F.Nondegenerate := nondegenerate_of_posDef hsymm hpd
  obtain ⟨n, b, hHspan⟩ := exists_basis_of_isLattice hlat
  have hn : n = 15 := by
    have hcard := Module.finrank_eq_card_basis b
    rw [hrank, Fintype.card_fin] at hcard
    exact hcard.symm
  subst hn
  subst hHspan
  -- the lattice is integral, so the Gram matrix of the basis is an integer matrix
  have hbmem : ∀ i, b i ∈ Submodule.span ℤ (Set.range (b : Fin 15 → X)) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  have hintegral : ∀ i j, F (b i) (b j) ∈ (1 : Submodule ℤ ℚ) := by
    intro i j
    exact (le_of_eq hself.symm) (hbmem i) _ (hbmem j)
  set A : Matrix (Fin 15) (Fin 15) ℤ := fun i j => (F (b i) (b j)).num with hAdef
  have hA : ∀ i j, ((A i j : ℤ) : ℚ) = F (b i) (b j) := by
    intro i j
    obtain ⟨k, hk⟩ := mem_one_iff.mp (hintegral i j)
    rw [hAdef]
    simp only [← hk, Rat.num_intCast]
  -- the coordinate isomorphism
  have hli : LinearIndependent ℤ (b : Fin 15 → X) :=
    (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).mpr b.linearIndependent
  set bZ : Basis (Fin 15) ℤ (Submodule.span ℤ (Set.range (b : Fin 15 → X))) :=
    Basis.span hli with hbZ
  have hbZcoe : ∀ i, ((bZ i : Submodule.span ℤ (Set.range (b : Fin 15 → X))) : X) = b i := by
    intro i
    rw [hbZ, Basis.span_apply]
  have hcoe : ∀ v : Fin 15 → ℤ,
      ((bZ.equivFun.symm v : Submodule.span ℤ (Set.range (b : Fin 15 → X))) : X)
        = coordSum (b : Fin 15 → X) v := by
    intro v
    rw [Basis.equivFun_symm_apply, coordSum_eq_zsmul_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [hbZcoe]
  have hsymmSpan : ∀ u : Submodule.span ℤ (Set.range (b : Fin 15 → X)),
      coordSum (b : Fin 15 → X) (bZ.equivFun u) = (u : X) := by
    intro u
    rw [← hcoe, LinearEquiv.symm_apply_apply]
  -- the transported matrix is symmetric
  have hAsymm : A.IsSymm := by
    ext i j
    have h1 := hA i j
    have h2 := hA j i
    have : ((A j i : ℤ) : ℚ) = ((A i j : ℤ) : ℚ) := by
      rw [h1, h2, hsymm.eq (b j) (b i)]
    exact_mod_cast this
  -- positive definiteness
  have hApd : ∀ v : Fin 15 → ℤ, v ≠ 0 → 0 < Matrix.toBilin' A v v := by
    intro v hv
    have hne : coordSum (b : Fin 15 → X) v ≠ 0 := fun h => hv (coordSum_eq_zero b.linearIndependent h)
    have hpos := hpd _ hne
    rw [← toBilin'_coordSum (F := F) b A hA v v] at hpos
    exact_mod_cast hpos
  -- oddness
  have hAodd : ∃ v : Fin 15 → ℤ, ¬ Even (Matrix.toBilin' A v v) := by
    obtain ⟨z, hz, k, hk, hkz⟩ := hodd
    refine ⟨bZ.equivFun ⟨z, hz⟩, ?_⟩
    have hcoord : coordSum (b : Fin 15 → X) (bZ.equivFun ⟨z, hz⟩) = z := hsymmSpan ⟨z, hz⟩
    have hval : ((Matrix.toBilin' A (bZ.equivFun ⟨z, hz⟩) (bZ.equivFun ⟨z, hz⟩) : ℤ) : ℚ)
        = (k : ℚ) := by
      rw [toBilin'_coordSum (F := F) b A hA, hcoord, hkz]
    have : Matrix.toBilin' A (bZ.equivFun ⟨z, hz⟩) (bZ.equivFun ⟨z, hz⟩) = k := by
      exact_mod_cast hval
    rw [this]
    exact hk
  -- unimodularity
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
    · intro ψ
      set c : Fin 15 → ℤ := fun i => ψ (Pi.single i 1) with hc
      set dual : Fin 15 → X := fun i => F.dualBasis hnd b i with hdual
      have hdualspan : Submodule.span ℤ (Set.range dual) =
          Submodule.span ℤ (Set.range (b : Fin 15 → X)) := by
        rw [hdual, ← LinearMap.BilinForm.dualSubmodule_span_of_basis F hnd b]
        exact hself
      have hzmem : coordSum dual c ∈ Submodule.span ℤ (Set.range (b : Fin 15 → X)) := by
        rw [← hdualspan]
        exact coordSum_mem_span dual c
      set v : Fin 15 → ℤ := bZ.equivFun ⟨coordSum dual c, hzmem⟩ with hv
      have hvcoord : coordSum (b : Fin 15 → X) v = coordSum dual c :=
        hsymmSpan ⟨coordSum dual c, hzmem⟩
      refine ⟨v, ?_⟩
      refine LinearMap.ext fun w => ?_
      -- both sides agree after casting to `ℚ`
      have hzb : ∀ j, F (coordSum dual c) (b j) = (c j : ℚ) := by
        intro j
        rw [show coordSum dual c = ∑ i, (c i : ℚ) • dual i from rfl, map_sum,
          LinearMap.sum_apply]
        rw [Finset.sum_eq_single j]
        · rw [map_smul, LinearMap.smul_apply, hdual, smul_eq_mul,
            LinearMap.BilinForm.apply_dualBasis_left hnd b j j, if_pos rfl, mul_one]
        · intro i _ hij
          rw [map_smul, LinearMap.smul_apply, hdual, smul_eq_mul,
            LinearMap.BilinForm.apply_dualBasis_left hnd b i j, if_neg (Ne.symm hij), mul_zero]
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      have hsingle : ∀ (j : Fin 15) (a : ℤ),
          (Pi.single j a : Fin 15 → ℤ) = a • (Pi.single j 1 : Fin 15 → ℤ) := by
        intro j a
        funext i
        by_cases h : i = j <;> simp [h]
      have hψw : ψ w = ∑ j, w j * c j := by
        have hw : w = ∑ j, w j • (Pi.single j 1 : Fin 15 → ℤ) := by
          conv_lhs => rw [← Finset.univ_sum_single w]
          exact Finset.sum_congr rfl fun j _ => hsingle j (w j)
        conv_lhs => rw [hw]
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, hc]
      have hexp : F (coordSum dual c) (coordSum (b : Fin 15 → X) w)
          = ∑ j, (w j : ℚ) * (c j : ℚ) := by
        rw [show coordSum (b : Fin 15 → X) w = ∑ j, (w j : ℚ) • b j from rfl, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_eq_mul, hzb j]
      have hlhs : ((Matrix.toBilin' A v w : ℤ) : ℚ) = ((∑ j, w j * c j : ℤ) : ℚ) := by
        rw [toBilin'_coordSum (F := F) b A hA, hvcoord, hexp]
        push_cast
        rfl
      have : Matrix.toBilin' A v w = ∑ j, w j * c j := by exact_mod_cast hlhs
      rw [this, hψw]
  -- assemble the host
  refine ⟨{ carrier := ModuleCat.of ℤ (Fin 15 → ℤ)
            pairing := Matrix.toBilin' A
            symmetric := toBilin'_isSymm A hAsymm
            positiveDefinite := hApd
            odd := hAodd
            unimodular := hAbij
            rank := Module.finrank_fin_fun ℤ },
      bZ.equivFun.toLinearMap, bZ.equivFun.injective, ?_⟩
  intro u v
  show ((Matrix.toBilin' A (bZ.equivFun u) (bZ.equivFun v) : ℤ) : ℚ) = F (u : X) (v : X)
  rw [toBilin'_coordSum (F := F) b A hA, hsymmSpan u, hsymmSpan v]

end Transport

/-! ## Rank and the glue construction -/

section GlueTransport

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]
variable {B : LinearMap.BilinForm ℚ W} {C : LinearMap.BilinForm ℚ U}
variable {N : Submodule ℤ W} {M : Submodule ℤ U}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A lattice has the rank of the ambient space. -/
theorem finrank_of_isLattice {X : Type*} [AddCommGroup X] [Module ℚ X]
    {H : Submodule ℤ X} (hH : IsLattice ℚ H) :
    Module.finrank ℤ H = Module.finrank ℚ X := by
  obtain ⟨n, b, rfl⟩ := exists_basis_of_isLattice hH
  have hli : LinearIndependent ℤ (b : Fin n → X) :=
    (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).mpr b.linearIndependent
  have h1 : Module.finrank ℤ (Submodule.span ℤ (Set.range (b : Fin n → X))) = n := by
    have hc := Module.finrank_eq_card_basis (Basis.span hli)
    rwa [Fintype.card_fin] at hc
  rw [h1, Module.finrank_eq_card_basis b, Fintype.card_fin]

omit [DecidableEq ι] in
/-- **`glue_finrank`.**  The glue lattice has the rank of the orthogonal sum. -/
theorem GlueSystem.glue_finrank (S : GlueSystem B C N M ι)
    (hN : IsLattice ℚ N) (hM : IsLattice ℚ M) :
    Module.finrank ℤ (glueLattice N M S.gen) = Module.finrank ℚ (W × U) :=
  finrank_of_isLattice (S.glue_isLattice hN hM)

/-- **Theorem H together with the basis transport of §2.7.**  A glue system in a
`15`-dimensional positive-definite orthogonal sum, whose first lattice carries a
vector of odd norm, produces an `SRG266.OddUnimodularLattice15` containing that
lattice isometrically.  Unimodularity of the host — `glue_unimodular_bijective`
of the design — is the `unimodular` field of the returned term, obtained from
`SRG266.Lattice.GlueSystem.glue_dual_eq_self`. -/
theorem GlueSystem.exists_host (S : GlueSystem B C N M ι)
    (hpdB : ∀ v : W, v ≠ 0 → 0 < B v v) (hpdC : ∀ v : U, v ≠ 0 → 0 < C v v)
    (hN : IsLattice ℚ N) (hM : IsLattice ℚ M)
    (hrank : Module.finrank ℚ (W × U) = 15)
    (hodd : ∃ z ∈ N, ∃ k : ℤ, ¬ Even k ∧ (k : ℚ) = B z z) :
    ∃ (L : OddUnimodularLattice15) (e : N →ₗ[ℤ] L.carrier), Function.Injective e ∧
      ∀ u v : N, ((L.pairing (e u) (e v) : ℤ) : ℚ) = B (u : W) (v : W) := by
  have hHodd : ∃ z ∈ glueLattice N M S.gen, ∃ k : ℤ,
      ¬ Even k ∧ (k : ℚ) = prodForm B C z z := by
    obtain ⟨z, hz, k, hk, hkz⟩ := hodd
    refine ⟨(z, 0), prod_le_glueLattice (Submodule.mem_prod.mpr ⟨hz, M.zero_mem⟩), k, hk, ?_⟩
    rw [prodForm_apply, hkz]
    simp
  obtain ⟨L, e, hinj, hpair⟩ := exists_oddUnimodularLattice15
    (prodForm_isSymm S.symmB S.symmC) (prodForm_posDef hpdB hpdC) hrank
    (S.glue_isLattice hN hM) S.glue_dual_eq_self hHodd
  refine ⟨L, e.comp (inclLeft N M S.gen), hinj.comp (inclLeft_injective N M S.gen), ?_⟩
  intro u v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hpair, inclLeft_coe, inclLeft_coe,
    prodForm_apply]
  simp

end GlueTransport

end SRG266.Lattice
