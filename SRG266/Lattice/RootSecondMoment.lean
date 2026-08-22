/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.NormTwoRootSeparator
import Mathlib.Algebra.Module.Torsion.Free

/-!
# Algebraic consequences of the norm-two root second moment

The degree-two weighted-theta calculation used by the SRG266 argument has a
very small algebraic output.  If `R` is the set of norm-two vectors of an
integral unimodular lattice, it asserts an identity of bilinear forms

`sum_{r in R} <r,x><r,y> = c <x,y>`.

This file separates the consequences that require no modular forms.  The
identity reconstructs `c x` as a linear combination of the roots.  When
`c != 0`, torsion-freeness therefore forces the roots to have full rank.
Finiteness of the root set and the existence of a separating integral
functional were already proved directly from positive definiteness.
-/

namespace SRG266
namespace Lattice

/-- The exact second-moment identity for the norm-two vectors of `L`. -/
def RootSecondMomentIdentity {n : ℕ} (L : PDUnimodularLattice n)
    (c : ℤ) : Prop :=
  ∀ x y : L.carrier,
    (∑ r : NormTwoRoot L, L.pairing r.1 x * L.pairing r.1 y) =
      c * L.pairing x y

/-- The second-moment identity reconstructs `c x` as an integral linear
combination of norm-two roots. -/
theorem rootSecondMoment_reconstruction {n : ℕ}
    (L : PDUnimodularLattice n) {c : ℤ}
    (h : RootSecondMomentIdentity L c) (x : L.carrier) :
    ∑ r : NormTwoRoot L, (L.pairing r.1 x) • r.1 = c • x := by
  apply L.unimodular.1
  ext y
  simpa only [map_sum, LinearMap.sum_apply, map_zsmul,
    LinearMap.smul_apply, smul_eq_mul]
    using h x y

/-- A nonzero second-moment scalar forces every scalar multiple `c x` into
the integral span of the roots. -/
theorem smul_mem_normTwoRootSpan_of_secondMoment {n : ℕ}
    (L : PDUnimodularLattice n) {c : ℤ}
    (h : RootSecondMomentIdentity L c) (x : L.carrier) :
    c • x ∈ normTwoRootSpan L := by
  rw [← rootSecondMoment_reconstruction L h x]
  exact Submodule.sum_mem _ fun r _ =>
    (normTwoRootSpan L).toAddSubgroup.zsmul_mem
      (Submodule.subset_span (Set.mem_range_self r)) _

/-- Multiplication by the second-moment scalar, regarded as an additive map
into the root span.  It is converted to a linear map with `toZLinearMap`, so
the construction is independent of the chosen `Module ℤ` instances. -/
noncomputable def secondMomentSpanAddHom {n : ℕ}
    (L : PDUnimodularLattice n) {c : ℤ}
    (h : RootSecondMomentIdentity L c) :
    L.carrier →+ normTwoRootSpan L where
  toFun x := ⟨c • x, smul_mem_normTwoRootSpan_of_secondMoment L h x⟩
  map_zero' := by
    apply Subtype.ext
    change c • (0 : L.carrier) = 0
    exact zsmul_zero c
  map_add' x y := by
    apply Subtype.ext
    change c • (x + y) = c • x + c • y
    exact zsmul_add x y c

/-- A nonzero second-moment identity implies that the norm-two roots span a
full-rank submodule. -/
theorem normTwoRoots_fullRank_of_secondMoment {n : ℕ}
    (L : PDUnimodularLattice n) {c : ℤ} (hc : c ≠ 0)
    (h : RootSecondMomentIdentity L c) :
    Set.finrank ℤ (Set.range (@normTwoRootVal n L)) = n := by
  letI := L.moduleFree
  letI := L.moduleFinite
  let S := normTwoRootSpan L
  letI : Module ℤ S := S.module
  letI : Module.Finite ℤ S := by
    dsimp only [S]
    exact Module.Finite.span_of_finite ℤ
      (Set.finite_range (@normTwoRootVal n L))
  let f : L.carrier →ₗ[ℤ] S :=
    toZLinearMap (secondMomentSpanAddHom L h)
  letI : IsAddTorsionFree L.carrier :=
    IsAddTorsionFree.of_isTorsionFree ℤ L.carrier
  have hinj : Function.Injective f := by
    intro x y hxy
    apply zsmul_right_injective hc
    exact congrArg Subtype.val hxy
  have hlower : Module.finrank ℤ L.carrier ≤
      Module.finrank ℤ S :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have hupper : Module.finrank ℤ S ≤
      Module.finrank ℤ L.carrier :=
    Submodule.finrank_le S
  unfold Set.finrank
  change Module.finrank ℤ S = n
  have hrank := L.rank
  omega

end Lattice
end SRG266
