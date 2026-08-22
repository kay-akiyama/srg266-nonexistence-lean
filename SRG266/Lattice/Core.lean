/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Localization.Module

/-!
# Shared lattice conventions

This module fixes the conventions every later lattice development in the
repository uses, so that the instance discipline is settled once instead of
being rediscovered in each consumer.

There are three independent settings in sections that share only
naming and instance conventions.

* Section A: an additive group `M` carrying an integral bilinear form
  `B : LinearMap.BilinForm ℤ M`.  This is the setting of
  `SRG266.OddUnimodularLattice15`.  The main result is the *norm-one
  splitting* `exists_normOneSplitting`: a positive-definite unimodular
  integral form splits off a maximal orthonormal family, leaving a
  norm-one-free core on which the form is again unimodular.
* Section B: a `ℤ`-lattice inside a vector space over a field of fractions.
  The definitions copy the instance shape of
  `Mathlib/LinearAlgebra/BilinearForm/DualLattice.lean` verbatim, namely
  `[Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]`.  The main
  result is `dual_dual`, the double-dual identity for an arbitrary lattice
  rather than only for the span of a basis.
* Section C: a `ℤ`-module quotient `P/N` cut out by a denominator bound
  `n • P ⊆ N`.  The main result is `finite_quotient_of_nsmul_le`: such a
  quotient is finite, so its cardinality is a bounded `ℕ`-valued invariant.
  This is what makes an index-maximisation argument over intermediate
  lattices possible.

## Instance discipline

The carriers in Section A are declared as `[AddCommGroup M]` only.  A
`Module ℤ M` instance is *never* assumed alongside it: the canonical
`AddCommGroup.toIntModule` is already available and adding a second one
creates a diamond that defeats unification against
`SRG266.OddUnimodularLattice15.carrier`.  Where a bundled `ModuleCat ℤ`
carrier has to be bridged to the abstract statements, the bridge is
`Subsingleton.elim` on the two `Module ℤ` instances; see
`SRG266/Lattice/HostBuilder.lean`.
-/

namespace SRG266.Lattice

/-! ## Section A — an integral bilinear form on an additive group -/

section IntegralForm

variable {M : Type*} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)

/-- The orthogonal complement of a single vector, as a `ℤ`-submodule. -/
def perp (v : M) : Submodule ℤ M := LinearMap.ker (B v)

@[simp]
theorem mem_perp {B : LinearMap.BilinForm ℤ M} {v w : M} :
    w ∈ perp B v ↔ B v w = 0 := Iff.rfl

/-- The restriction of a form to a submodule evaluates by coercion. -/
@[simp]
theorem restrict_apply_coe (N : Submodule ℤ M) (x y : N) :
    (B.restrict N) x y = B (x : M) (y : M) := rfl

/-- A positive-definite form is nonnegative on the diagonal. -/
theorem nonneg_of_posDef (hpd : ∀ v : M, v ≠ 0 → 0 < B v v) (v : M) : 0 ≤ B v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (hpd v hv).le

/-- Two norm-one vectors of a positive-definite integral form pair to
`-1`, `0` or `1`.  This is the integral Cauchy--Schwarz step. -/
theorem inner_normOne_normOne_cases (hsymm : B.IsSymm)
    (hpd : ∀ v : M, v ≠ 0 → 0 < B v v) {u w : M}
    (hu : B u u = 1) (hw : B w w = 1) :
    B u w = -1 ∨ B u w = 0 ∨ B u w = 1 := by
  set a : ℤ := B u w with ha
  have hwu : B w u = a := by rw [ha, hsymm.eq u w]
  have hnonneg : 0 ≤ B (u - a • w) (u - a • w) := nonneg_of_posDef B hpd _
  have hexpand : B (u - a • w) (u - a • w) = 1 - a * a := by
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, hu, hw, hwu, ← ha]
    ring
  rw [hexpand] at hnonneg
  have hlower : -2 < a := by
    by_contra h
    have : a ≤ -2 := by omega
    nlinarith
  have hupper : a < 2 := by
    by_contra h
    have : 2 ≤ a := by omega
    nlinarith
  omega

/-- Norm-one vectors pairing to `1` are equal. -/
theorem eq_of_inner_normOne_eq_one (hsymm : B.IsSymm)
    (hpd : ∀ v : M, v ≠ 0 → 0 < B v v) {u w : M}
    (hu : B u u = 1) (hw : B w w = 1) (huw : B u w = 1) : u = w := by
  by_contra hne
  have hsub : u - w ≠ 0 := sub_ne_zero_of_ne hne
  have hpos := hpd _ hsub
  have hwu : B w u = 1 := by rw [← hsymm.eq u w, huw]
  have hzero : B (u - w) (u - w) = 0 := by
    simp only [map_sub, LinearMap.sub_apply, hu, hw, huw, hwu]
    ring
  omega

/-- A vector of norm one spans a direct complement of its orthogonal
complement. -/
theorem isCompl_span_perp {v : M} (hv : B v v = 1) :
    IsCompl (Submodule.span ℤ {v}) (perp B v) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hax : a * B v v = 0 := by
      have := mem_perp.mp hx'
      simpa [map_smul, smul_eq_mul] using this
    rw [hv, mul_one] at hax
    simp [hax]
  · rw [codisjoint_iff_le_sup]
    intro x _
    refine Submodule.mem_sup.mpr ⟨(B v x) • v, Submodule.mem_span_singleton.mpr ⟨_, rfl⟩,
      x - (B v x) • v, ?_, by abel⟩
    have : B v (x - (B v x) • v) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, hv, mul_one, sub_self]
    exact mem_perp.mpr this

/-! ### Orthonormal families and the norm-one splitting -/

/-- A finite family of pairwise orthogonal norm-one vectors. -/
structure IsOrthonormal {k : ℕ} (u : Fin k → M) : Prop where
  /-- Every member of the family has norm one. -/
  norm : ∀ i, B (u i) (u i) = 1
  /-- Distinct members are orthogonal. -/
  orthogonal : ∀ i j, i ≠ j → B (u i) (u j) = 0

/-- The common orthogonal complement of a finite family. -/
def unitPerp {k : ℕ} (u : Fin k → M) : Submodule ℤ M := ⨅ i, perp B (u i)

@[simp]
theorem mem_unitPerp {B : LinearMap.BilinForm ℤ M} {k : ℕ} {u : Fin k → M} {w : M} :
    w ∈ unitPerp B u ↔ ∀ i, B (u i) w = 0 := by
  simp [unitPerp, Submodule.mem_iInf]

variable {B}

/-- An orthonormal family is `ℤ`-linearly independent. -/
theorem IsOrthonormal.linearIndependent {k : ℕ} {u : Fin k → M}
    (hu : IsOrthonormal B u) : LinearIndependent ℤ u := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hj := congrArg (fun x => B (u j) x) hg
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hj
  rw [Finset.sum_eq_single j] at hj
  · simpa [hu.norm j] using hj
  · intro i _ hij
    rw [hu.orthogonal j i (Ne.symm hij), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The orthogonal projection formula: subtracting the coordinates along an
orthonormal family lands in the common orthogonal complement. -/
theorem IsOrthonormal.sub_proj_mem {k : ℕ} {u : Fin k → M}
    (hu : IsOrthonormal B u) (v : M) :
    v - ∑ i, B (u i) v • u i ∈ unitPerp B u := by
  rw [mem_unitPerp]
  intro j
  rw [map_sub, map_sum]
  have hterm : ∀ i, (B (u j)) ((B (u i)) v • u i) = (B (u i)) v * (B (u j)) (u i) := by
    intro i
    rw [map_smul, smul_eq_mul]
  simp_rw [hterm]
  rw [Finset.sum_eq_single j]
  · rw [hu.norm j, mul_one, sub_self]
  · intro i _ hij
    rw [hu.orthogonal j i (Ne.symm hij), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- A vector of the common orthogonal complement has vanishing coordinates. -/
theorem proj_eq_zero_of_mem_unitPerp {k : ℕ} {u : Fin k → M}
    {w : M} (hw : w ∈ unitPerp B u) :
    ∑ i, B (u i) w • u i = 0 := by
  rw [mem_unitPerp] at hw
  refine Finset.sum_eq_zero ?_
  intro i _
  rw [hw i, zero_smul]

/-- The span of an orthonormal family and its orthogonal complement are
complementary submodules. -/
theorem IsOrthonormal.isCompl {k : ℕ} {u : Fin k → M} (hu : IsOrthonormal B u) :
    IsCompl (Submodule.span ℤ (Set.range u)) (unitPerp B u) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    rw [mem_unitPerp] at hx'
    have hzero : ∀ j, g j = 0 := by
      intro j
      have hj := hx' j
      simp only [map_sum, map_smul, smul_eq_mul] at hj
      rw [Finset.sum_eq_single j] at hj
      · simpa [hu.norm j] using hj
      · intro i _ hij
        rw [hu.orthogonal j i (Ne.symm hij), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    simp [hzero]
  · rw [codisjoint_iff_le_sup]
    intro x _
    refine Submodule.mem_sup.mpr
      ⟨∑ i, B (u i) x • u i, ?_, x - ∑ i, B (u i) x • u i, hu.sub_proj_mem x, by abel⟩
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable (B)

/-- A maximal orthonormal family exists: an orthonormal family whose
orthogonal complement contains no norm-one vector. -/
theorem exists_maximal_orthonormal [Module.Finite ℤ M] (hsymm : B.IsSymm) :
    ∃ (k : ℕ) (u : Fin k → M), IsOrthonormal B u ∧
      ∀ w ∈ unitPerp B u, B w w ≠ 1 := by
  classical
  set n : ℕ := Module.finrank ℤ M with hn
  set P : ℕ → Prop := fun k => ∃ u : Fin k → M, IsOrthonormal B u with hP
  have hbound : ∀ k, P k → k ≤ n := by
    rintro k ⟨u, hu⟩
    simpa using hu.linearIndependent.fintype_card_le_finrank
  have hzero : P 0 :=
    ⟨fun i => Fin.elim0 i, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩
  set m : ℕ := Nat.findGreatest P n with hm
  obtain ⟨u, hu⟩ : P m := Nat.findGreatest_spec (Nat.zero_le n) hzero
  refine ⟨m, u, hu, ?_⟩
  intro w hw hnorm
  have hwperp : ∀ i, B (u i) w = 0 := mem_unitPerp.mp hw
  have hnext : P (m + 1) := by
    refine ⟨Fin.snoc u w, ⟨?_, ?_⟩⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last]
        exact hnorm
      · intro j
        rw [Fin.snoc_castSucc]
        exact hu.norm j
    · intro i j
      refine Fin.lastCases ?_ ?_ i
      · refine Fin.lastCases ?_ ?_ j
        · intro hij
          exact absurd rfl hij
        · intro j' _
          rw [Fin.snoc_last, Fin.snoc_castSucc, ← hsymm.eq (u j') w]
          exact hwperp j'
      · intro i'
        refine Fin.lastCases ?_ ?_ j
        · intro _
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          exact hwperp i'
        · intro j' hij
          have hij' : i' ≠ j' := by
            intro h
            exact hij (by rw [h])
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hu.orthogonal i' j' hij'
  exact Nat.findGreatest_is_greatest (by omega) (hbound _ hnext) hnext

/-- The projection onto the orthogonal complement of an orthonormal family,
before restricting the codomain. -/
def orthoProjAux {k : ℕ} (u : Fin k → M) : M →ₗ[ℤ] M :=
  LinearMap.id - ∑ i, (B (u i)).smulRight (u i)

@[simp]
theorem orthoProjAux_apply {k : ℕ} (u : Fin k → M) (v : M) :
    orthoProjAux B u v = v - ∑ i, B (u i) v • u i := by
  simp [orthoProjAux, LinearMap.sum_apply]

/-- The linear projection onto the orthogonal complement of an orthonormal
family. -/
def orthoProj {k : ℕ} {u : Fin k → M} (hu : IsOrthonormal B u) :
    M →ₗ[ℤ] unitPerp B u :=
  LinearMap.codRestrict _ (orthoProjAux B u) (by
    intro v
    simpa using hu.sub_proj_mem v)

@[simp]
theorem orthoProj_coe {k : ℕ} {u : Fin k → M} (hu : IsOrthonormal B u) (v : M) :
    ((orthoProj B hu v : unitPerp B u) : M) = v - ∑ i, B (u i) v • u i := by
  simp [orthoProj]

/-- On the orthogonal complement the projection is the identity. -/
theorem orthoProj_of_mem {k : ℕ} {u : Fin k → M} (hu : IsOrthonormal B u)
    (w : unitPerp B u) : orthoProj B hu (w : M) = w := by
  apply Subtype.ext
  rw [orthoProj_coe, proj_eq_zero_of_mem_unitPerp w.2, sub_zero]

/-- Unimodularity descends to the orthogonal complement of an orthonormal
family. -/
theorem restrict_unitPerp_bijective {k : ℕ} {u : Fin k → M}
    (hu : IsOrthonormal B u) (hsymm : B.IsSymm) (hbij : Function.Bijective B) :
    Function.Bijective (B.restrict (unitPerp B u)) := by
  constructor
  · intro w w' hww'
    have hzero : ∀ z : unitPerp B u, B ((w : M) - (w' : M)) (z : M) = 0 := by
      intro z
      have hz := congrArg (fun f => f z) hww'
      simp only [restrict_apply_coe] at hz
      simp only [map_sub, LinearMap.sub_apply]
      rw [hz, sub_self]
    have hunits : ∀ i, B ((w : M) - (w' : M)) (u i) = 0 := by
      intro i
      rw [← hsymm.eq (u i) ((w : M) - (w' : M))]
      have hw := mem_unitPerp.mp w.2 i
      have hw' := mem_unitPerp.mp w'.2 i
      simp only [map_sub]
      rw [hw, hw', sub_self]
    have hall : ∀ v : M, B ((w : M) - (w' : M)) v = 0 := by
      intro v
      have h1 : B ((w : M) - (w' : M)) (v - ∑ i, B (u i) v • u i) = 0 :=
        hzero ⟨_, hu.sub_proj_mem v⟩
      have h3 : B ((w : M) - (w' : M)) (∑ i, B (u i) v • u i) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero ?_
        intro i _
        rw [map_smul, hunits i, smul_zero]
      rw [map_sub, h3, sub_zero] at h1
      exact h1
    have hlin : B ((w : M) - (w' : M)) = B 0 := by
      rw [map_zero]
      ext v
      simpa using hall v
    exact Subtype.ext (sub_eq_zero.mp (hbij.1 hlin))
  · intro φ
    obtain ⟨z, hz⟩ := hbij.2 (φ ∘ₗ orthoProj B hu)
    refine ⟨orthoProj B hu z, ?_⟩
    ext w
    have hzw : B z (w : M) = φ (orthoProj B hu (w : M)) := by
      have := congrArg (fun f => f (w : M)) hz
      simpa using this
    have hvanish : B (∑ i, B (u i) z • u i) (w : M) = 0 := by
      rw [map_sum]
      simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero ?_
      intro i _
      rw [mem_unitPerp.mp w.2 i, mul_zero]
    simp only [restrict_apply_coe, orthoProj_coe, map_sub, LinearMap.sub_apply]
    rw [hvanish, sub_zero, hzw, orthoProj_of_mem]

/-- Unimodularity descends to the orthogonal complement of a single norm-one
vector.  This is the one-vector case of `restrict_unitPerp_bijective`. -/
theorem restrict_perp_bijective {v : M} (hv : B v v = 1) (hsymm : B.IsSymm)
    (hbij : Function.Bijective B) :
    Function.Bijective (B.restrict (perp B v)) := by
  have hu : IsOrthonormal B (fun _ : Fin 1 => v) :=
    ⟨fun _ => hv, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  have hperp : unitPerp B (fun _ : Fin 1 => v) = perp B v := by
    ext w
    rw [mem_unitPerp, mem_perp]
    exact ⟨fun h => h 0, fun h _ => h⟩
  have := restrict_unitPerp_bijective B hu hsymm hbij
  rwa [hperp] at this

/-- The span of all norm-one vectors of the form. -/
def unitSpan : Submodule ℤ M := Submodule.span ℤ {u : M | B u u = 1}

theorem subset_unitSpan {u : M} (hu : B u u = 1) : u ∈ unitSpan B :=
  Submodule.subset_span hu

/-- The output object of the norm-one splitting: a maximal orthonormal family
together with the properties of its orthogonal complement. -/
structure NormOneSplitting (B : LinearMap.BilinForm ℤ M) where
  /-- The number of orthonormal units split off. -/
  rank : ℕ
  /-- The orthonormal units. -/
  units : Fin rank → M
  /-- The units are orthonormal. -/
  orthonormal : IsOrthonormal B units
  /-- The core carries no norm-one vector. -/
  core_normOneFree : ∀ w ∈ unitPerp B units, B w w ≠ 1
  /-- The form restricted to the core is again unimodular. -/
  core_unimodular : Function.Bijective (B.restrict (unitPerp B units))

namespace NormOneSplitting

variable {B}

/-- The norm-one-free core of a splitting. -/
def core (S : NormOneSplitting B) : Submodule ℤ M := unitPerp B S.units

theorem units_norm (S : NormOneSplitting B) (i : Fin S.rank) :
    B (S.units i) (S.units i) = 1 := S.orthonormal.norm i

theorem units_orthogonal (S : NormOneSplitting B) {i j : Fin S.rank} (h : i ≠ j) :
    B (S.units i) (S.units j) = 0 := S.orthonormal.orthogonal i j h

theorem units_core_orthogonal (S : NormOneSplitting B) (i : Fin S.rank)
    {w : M} (hw : w ∈ S.core) : B (S.units i) w = 0 :=
  mem_unitPerp.mp hw i

/-- Every vector decomposes as an integral combination of the units plus a
core vector, with the coordinates given by the pairing. -/
theorem decompose (S : NormOneSplitting B) (v : M) :
    v - ∑ i, B (S.units i) v • S.units i ∈ S.core :=
  S.orthonormal.sub_proj_mem v

/-- The span of the units is complementary to the core. -/
theorem isCompl (S : NormOneSplitting B) :
    IsCompl (Submodule.span ℤ (Set.range S.units)) S.core :=
  S.orthonormal.isCompl

/-- The coordinates in the decomposition are unique. -/
theorem coeff_unique (S : NormOneSplitting B) (v : M) (a : Fin S.rank → ℤ)
    {w : M} (hw : w ∈ S.core)
    (hv : v = ∑ i, a i • S.units i + w) (j : Fin S.rank) :
    a j = B (S.units j) v := by
  have hj := congrArg (fun x => B (S.units j) x) hv
  simp only [map_add, map_sum, map_smul, smul_eq_mul] at hj
  rw [Finset.sum_eq_single j] at hj
  · rw [S.units_norm j, mul_one, S.units_core_orthogonal j hw, add_zero] at hj
    exact hj.symm
  · intro i _ hij
    rw [S.units_orthogonal (Ne.symm hij), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The rank of the core complements the number of units. -/
theorem finrank_core_add [Module.Finite ℤ M] (S : NormOneSplitting B) :
    Module.finrank ℤ S.core + S.rank = Module.finrank ℤ M := by
  classical
  have hspan : Module.finrank ℤ (Submodule.span ℤ (Set.range S.units)) = S.rank := by
    simpa using finrank_span_eq_card S.orthonormal.linearIndependent
  have hquot := Submodule.finrank_quotient_add_finrank
    (Submodule.span ℤ (Set.range S.units))
  rw [(Submodule.quotientEquivOfIsCompl _ _ S.isCompl).finrank_eq, hspan] at hquot
  exact hquot

/-- For a maximal splitting the units span every norm-one vector:
`unitSpan` is exactly the span of the chosen orthonormal family. -/
theorem unitSpan_eq (S : NormOneSplitting B) (hsymm : B.IsSymm)
    (hpd : ∀ v : M, v ≠ 0 → 0 < B v v) :
    unitSpan B = Submodule.span ℤ (Set.range S.units) := by
  refine le_antisymm ?_ ?_
  · rw [unitSpan, Submodule.span_le]
    intro w hw
    have hw1 : B w w = 1 := hw
    have hcmem : w - ∑ i, B (S.units i) w • S.units i ∈ S.core := S.decompose w
    set c : M := w - ∑ i, B (S.units i) w • S.units i with hc
    have hcunit : ∀ i, B c (S.units i) = 0 := by
      intro i
      rw [← hsymm.eq (S.units i) c]
      exact S.units_core_orthogonal i hcmem
    have hkey : ∀ z : M, B z c = B z w - ∑ i, B (S.units i) w * B z (S.units i) := by
      intro z
      rw [hc, map_sub, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.map_smul, smul_eq_mul]
    have hcc : B c c = B c w := by
      rw [hkey c]
      have hz : ∀ i : Fin S.rank, B (S.units i) w * B c (S.units i) = 0 := by
        intro i
        rw [hcunit i, mul_zero]
      simp_rw [hz]
      simp
    have hwc : B w c = 1 - ∑ i, B (S.units i) w * B (S.units i) w := by
      rw [hkey w, hw1]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [hsymm.eq w (S.units i)]
    have hccval : B c c = 1 - ∑ i, B (S.units i) w * B (S.units i) w := by
      rw [hcc, hsymm.eq c w, hwc]
    have hnonneg : 0 ≤ B c c := nonneg_of_posDef B hpd c
    have hne : B c c ≠ 1 := S.core_normOneFree c hcmem
    have hsq : 0 ≤ ∑ i, B (S.units i) w * B (S.units i) w :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hzero : B c c = 0 := by omega
    have hc0 : c = 0 := by
      by_contra hcne
      exact absurd hzero (ne_of_gt (hpd c hcne))
    have hwsum : w = ∑ i, B (S.units i) w • S.units i := by
      rw [hc, sub_eq_zero] at hc0
      exact hc0
    rw [hwsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact subset_unitSpan B (S.units_norm i)

/-- The unit span and the core have complementary ranks. -/
theorem finrank_unitSpan_add_finrank_core [Module.Finite ℤ M]
    (S : NormOneSplitting B) (hsymm : B.IsSymm)
    (hpd : ∀ v : M, v ≠ 0 → 0 < B v v) :
    Module.finrank ℤ (unitSpan B) + Module.finrank ℤ S.core = Module.finrank ℤ M := by
  classical
  rw [S.unitSpan_eq hsymm hpd]
  have hspan : Module.finrank ℤ (Submodule.span ℤ (Set.range S.units)) = S.rank := by
    simpa using finrank_span_eq_card S.orthonormal.linearIndependent
  rw [hspan, Nat.add_comm]
  exact S.finrank_core_add

end NormOneSplitting

/-- **Norm-one splitting.**  A positive-definite unimodular integral form on a
finitely generated group splits off a maximal orthonormal family, leaving a
norm-one-free unimodular core. -/
theorem exists_normOneSplitting [Module.Finite ℤ M] (hsymm : B.IsSymm)
    (hbij : Function.Bijective B) :
    Nonempty (NormOneSplitting B) := by
  obtain ⟨k, u, hu, hfree⟩ := exists_maximal_orthonormal B hsymm
  exact ⟨{ rank := k
           units := u
           orthonormal := hu
           core_normOneFree := hfree
           core_unimodular := restrict_unitPerp_bijective B hu hsymm hbij }⟩

/-- The elementary half of the splitting, stated for a single norm-one vector:
every vector is an integral multiple of `u` plus a vector orthogonal to `u`. -/
theorem norm_one_split {u : M} (hu : B u u = 1) (v : M) :
    ∃ (a : ℤ) (w : M), v = a • u + w ∧ B u w = 0 := by
  refine ⟨B u v, v - (B u v) • u, by abel, ?_⟩
  simp only [map_sub, map_smul, smul_eq_mul, hu, mul_one, sub_self]

end IntegralForm

/-! ## Section B — a lattice inside a vector space over a fraction field

The instance shape below is copied from
`Mathlib/LinearAlgebra/BilinearForm/DualLattice.lean`. -/

section RationalLattice

variable {R S W : Type*} [CommRing R] [Field S] [AddCommGroup W]
variable [Algebra R S] [Module R W] [Module S W] [IsScalarTower R S W]

/-- An `R`-lattice in the `S`-vector space `W`: finitely generated over `R`
and spanning over `S`. -/
structure IsLattice (S : Type*) [Field S] [Algebra R S] [Module S W]
    [IsScalarTower R S W] (N : Submodule R W) : Prop where
  /-- The lattice is finitely generated. -/
  fg : N.FG
  /-- The lattice spans the ambient space. -/
  spans : Submodule.span S (N : Set W) = ⊤

variable (B : LinearMap.BilinForm S W)

/-- Integrality of a form on a lattice: all pairings lie in the image of `R`. -/
def IsIntegral (N : Submodule R W) : Prop := N ≤ B.dualSubmodule N

theorem integral_iff_le_dual {N : Submodule R W} :
    IsIntegral B N ↔ N ≤ B.dualSubmodule N := Iff.rfl

theorem isIntegral_iff_forall {N : Submodule R W} :
    IsIntegral B N ↔ ∀ u ∈ N, ∀ v ∈ N, B u v ∈ (1 : Submodule R S) :=
  ⟨fun h _ hu v hv => h hu v hv, fun h _ hu v hv => h _ hu v hv⟩

end RationalLattice

section IntegerLattice

open Module

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable (B : LinearMap.BilinForm ℚ W)

/-- Every lattice is the `ℤ`-span of a `ℚ`-basis of the ambient space. -/
theorem exists_basis_of_isLattice {N : Submodule ℤ W} (hN : IsLattice ℚ N) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ W), N = Submodule.span ℤ (Set.range b) := by
  classical
  haveI : Module.Finite ℤ N := Module.Finite.iff_fg.mpr hN.fg
  haveI hnzW : NoZeroSMulDivisors ℤ W := by
    refine ⟨fun {c x} h => ?_⟩
    rcases eq_or_ne c 0 with hc | hc
    · exact Or.inl hc
    · refine Or.inr ?_
      have hq : ((c : ℚ)) • x = 0 := by
        rw [Int.cast_smul_eq_zsmul ℚ c x]
        exact h
      exact (smul_eq_zero.mp hq).resolve_left (Int.cast_ne_zero.mpr hc)
  haveI hnzN : NoZeroSMulDivisors ℤ (N : Type _) :=
    Function.Injective.noZeroSMulDivisors (N.subtype) Subtype.val_injective rfl
      (fun _ _ => rfl)
  obtain ⟨n, b0⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := N)
  set v : Fin n → W := fun i => ((b0 i : N) : W) with hv
  have hspanN : Submodule.span ℤ (Set.range v) = N := by
    have hmap : Submodule.map N.subtype (Submodule.span ℤ (Set.range b0)) =
        Submodule.span ℤ (Set.range v) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← hmap, b0.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hindepZ : LinearIndependent ℤ v :=
    b0.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  have hindep : LinearIndependent ℚ v :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hindepZ
  have hspanQ : Submodule.span ℚ (Set.range v) = ⊤ := by
    refine top_unique ?_
    rw [← hN.spans, Submodule.span_le, ← hspanN]
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Submodule.subset_span hy
    · exact Submodule.zero_mem _
    · intro y z _ _ hy hz
      exact Submodule.add_mem _ hy hz
    · intro a y _ hy
      have hcast : a • y = ((a : ℚ)) • y := by
        rw [← Int.cast_smul_eq_zsmul ℚ a y]
      rw [hcast]
      exact Submodule.smul_mem _ _ hy
  refine ⟨n, Basis.mk hindep (by rw [hspanQ]), ?_⟩
  rw [← hspanN]
  congr 1
  simp [Basis.coe_mk]

/-- **Double dual.**  For a nondegenerate symmetric form, the dual of the dual
of an arbitrary lattice is the lattice itself. -/
theorem dual_dual {N : Submodule ℤ W} (hN : IsLattice ℚ N)
    (hnd : B.Nondegenerate) (hsymm : B.IsSymm) :
    B.dualSubmodule (B.dualSubmodule N) = N := by
  obtain ⟨n, b, rfl⟩ := exists_basis_of_isLattice hN
  exact B.dualSubmodule_dualSubmodule_of_basis hnd hsymm b

/-- The dual of a lattice is a lattice. -/
theorem dual_isLattice {N : Submodule ℤ W} (hN : IsLattice ℚ N)
    (hnd : B.Nondegenerate) :
    IsLattice ℚ (B.dualSubmodule N) := by
  classical
  obtain ⟨n, b, rfl⟩ := exists_basis_of_isLattice hN
  haveI : Module.Finite ℚ W := Module.Finite.of_basis b
  rw [B.dualSubmodule_span_of_basis hnd b]
  refine ⟨⟨Finset.image (B.dualBasis hnd b) Finset.univ, ?_⟩, ?_⟩
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  · rw [Submodule.span_span_of_tower ℤ]
    exact (B.dualBasis hnd b).span_eq

end IntegerLattice

/-! ## Section C — finiteness of bounded-denominator quotients

A denominator bound `n • N^∨ ⊆ N` makes the dual quotient `N^∨/N` a finitely
generated `ℤ`-module killed by `n`, hence finite.  Finiteness is what turns the
index of an intermediate lattice into a bounded `ℕ`-valued invariant, which is
how a *maximal* integral overlattice is produced. -/

section BoundedTorsion

/-- A finitely generated `ℤ`-module annihilated by a nonzero natural number is
finite.  The `ℤ`-generating set is reinterpreted as a `ZMod n`-generating set,
which is legitimate because every additive subgroup of an `n`-torsion group is a
`ZMod n`-submodule. -/
theorem finite_of_nsmul_eq_zero {Q : Type*} [AddCommGroup Q] [Module.Finite ℤ Q]
    {n : ℕ} [NeZero n] (h : ∀ q : Q, n • q = 0) : Finite Q := by
  classical
  haveI : Module (ZMod n) Q := AddCommGroup.zmodModule h
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := Q)
  have hspan : Submodule.span (ZMod n) (S : Set Q) = ⊤ := by
    refine top_unique fun q _ => ?_
    have hq : q ∈ Submodule.span ℤ (S : Set Q) := by rw [hS]; exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
    · exact fun y hy => Submodule.subset_span hy
    · exact Submodule.zero_mem _
    · exact fun y z _ _ hy hz => Submodule.add_mem _ hy hz
    · intro a y _ hy
      rw [← Int.cast_smul_eq_zsmul (ZMod n) a y]
      exact Submodule.smul_mem _ _ hy
  haveI : Module.Finite (ZMod n) Q := ⟨⟨S, hspan⟩⟩
  exact Module.finite_of_finite (ZMod n)

/-- A denominator bound `n • P ⊆ N` says exactly that `n` annihilates the
quotient `P/N`. -/
theorem quotient_nsmul_eq_zero {W : Type*} [AddCommGroup W]
    {N P : Submodule ℤ W} {n : ℕ} (hsmul : ∀ y ∈ P, (n : ℤ) • y ∈ N)
    (q : P ⧸ N.comap P.subtype) : n • q = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap]
  have hy := hsmul (y : W) y.2
  rwa [Nat.cast_smul_eq_nsmul ℤ] at hy

/-- **Bounded denominators give a finite quotient.**  If `P` is a finitely
generated `ℤ`-submodule and `n • P ⊆ N` for some `n ≠ 0`, then `P/N` is
finite. -/
theorem finite_quotient_of_nsmul_le {W : Type*} [AddCommGroup W]
    {N P : Submodule ℤ W} (hP : P.FG) {n : ℕ} [NeZero n]
    (hsmul : ∀ y ∈ P, (n : ℤ) • y ∈ N) :
    Finite (P ⧸ N.comap P.subtype) := by
  haveI : Module.Finite ℤ P := Module.Finite.iff_fg.mpr hP
  haveI : Module.Finite ℤ (P ⧸ N.comap P.subtype) := Module.Finite.quotient ℤ _
  exact finite_of_nsmul_eq_zero (n := n) (quotient_nsmul_eq_zero hsmul)

end BoundedTorsion

end SRG266.Lattice
