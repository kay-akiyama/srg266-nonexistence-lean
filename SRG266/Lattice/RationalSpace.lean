/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.KernelRank
import SRG266.Lattice.Core
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.StdBasis

/-!
# The rational Gram space

`SRG266.IntegralGramLattice` is the quotient of `ℤ^220` by the radical of the
local Gram form.  Every lattice-theoretic argument beyond integrality needs the
ambient rational quadratic space in which that lattice sits, together with the
comparison map.  This file builds them.

* `ratGramSpace G x` is `ℚ^220` modulo `rationalGramKernel G x`, carrying the
  induced form `ratGramForm G x`.  Its dimension is `12`.
* `toRatSpace G x : IntegralGramLattice G x →ₗ[ℤ] ratGramSpace G x` is injective
  and preserves pairings, and its image `gramLattice G x` is a `ℤ`-lattice in
  the sense of `SRG266.Lattice.IsLattice`.

The lemma `ker_toBilin'_eq_ker_mulVecLin`
identifies the radical of a symmetric matrix form with the kernel of
multiplication by that matrix.  The integral instance of this statement is the
repository's `integralGramKernel_eq_relations`; the rational instance is what
lets `rationalGramKernel` — the submodule whose rank the repository already
computes — be used as the quotient.
-/

open scoped Matrix

namespace SRG266

/-! ### The radical of a symmetric matrix form -/

section KerCompare

variable {R ι : Type*} [CommRing R] [Fintype ι]

theorem vecMul_eq_mulVec_of_isSymm {A : Matrix ι ι R} (hA : A.IsSymm) (z : ι → R) :
    z ᵥ* A = A *ᵥ z := by
  rw [← Matrix.vecMul_transpose, hA.eq]

/-- For a symmetric matrix the radical of the associated bilinear form is the
kernel of multiplication by the matrix. -/
theorem ker_toBilin'_eq_ker_mulVecLin [DecidableEq ι] {A : Matrix ι ι R}
    (hA : A.IsSymm) :
    LinearMap.ker (Matrix.toBilin' A) = LinearMap.ker A.mulVecLin := by
  ext z
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hz
    refine dotProduct_eq_zero_iff.mp fun w => ?_
    have hw := congrArg (fun φ : (ι → R) →ₗ[R] R => φ w) hz
    simp only [LinearMap.zero_apply] at hw
    rwa [Matrix.toBilin'_apply', Matrix.dotProduct_mulVec,
      vecMul_eq_mulVec_of_isSymm hA] at hw
  · intro hz
    refine LinearMap.ext fun w => ?_
    rw [Matrix.toBilin'_apply', Matrix.dotProduct_mulVec,
      vecMul_eq_mulVec_of_isSymm hA, hz]
    simp

end KerCompare

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### The rational form on coordinate vectors -/

theorem localGramMatrixRat_isSymm (x : V) : (localGramMatrixRat G x).IsSymm :=
  Matrix.IsSymm.ext fun B C => by
    change ((localGramMatrix G x C B : ℤ) : ℚ) = ((localGramMatrix G x B C : ℤ) : ℚ)
    exact congrArg (fun n : ℤ => (n : ℚ)) (localGramMatrix_comm G x C B)

/-- The rational Gram form on coordinate vectors. -/
def ratGramFormOnPi (x : V) :
    LinearMap.BilinForm ℚ (SecondSubconstituent G x → ℚ) :=
  Matrix.toBilin' (localGramMatrixRat G x)

theorem ratGramFormOnPi_apply (x : V) (v w : SecondSubconstituent G x → ℚ) :
    ratGramFormOnPi G x v w = v ⬝ᵥ (localGramMatrixRat G x *ᵥ w) :=
  Matrix.toBilin'_apply' _ _ _

theorem ratGramFormOnPi_isSymm (x : V) : (ratGramFormOnPi G x).IsSymm := by
  rw [ratGramFormOnPi, Matrix.isSymm_toBilin'_iff_isSymm]
  exact localGramMatrixRat_isSymm G x

theorem ratGramFormOnPi_isRefl (x : V) : (ratGramFormOnPi G x).IsRefl :=
  (ratGramFormOnPi_isSymm G x).isRefl

theorem ker_ratGramFormOnPi (x : V) :
    LinearMap.ker (ratGramFormOnPi G x) = rationalGramKernel G x :=
  ker_toBilin'_eq_ker_mulVecLin (localGramMatrixRat_isSymm G x)

/-! ### The rational Gram space -/

/-- The ambient rational quadratic space of the local Gram lattice. -/
abbrev ratGramSpace (x : V) :=
  (SecondSubconstituent G x → ℚ) ⧸ rationalGramKernel G x

/-- The bilinear form induced on the rational Gram space. -/
def ratGramForm (x : V) : LinearMap.BilinForm ℚ (ratGramSpace G x) :=
  LinearMap.IsRefl.liftQ₂
    (ratGramFormOnPi G x)
    (rationalGramKernel G x)
    (ratGramFormOnPi_isRefl G x)
    (le_of_eq (ker_ratGramFormOnPi G x).symm)

@[simp]
theorem ratGramForm_mk (x : V) (v w : SecondSubconstituent G x → ℚ) :
    ratGramForm G x (Submodule.Quotient.mk v) (Submodule.Quotient.mk w) =
      v ⬝ᵥ (localGramMatrixRat G x *ᵥ w) :=
  ratGramFormOnPi_apply G x v w

theorem ratGramForm_isSymm (x : V) : (ratGramForm G x).IsSymm := by
  constructor
  intro v w
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact (ratGramFormOnPi_isSymm G x).eq v w

theorem ratGramForm_isRefl (x : V) : (ratGramForm G x).IsRefl :=
  (ratGramForm_isSymm G x).isRefl

theorem finrank_ratGramSpace (hG : IsHypothetical G) (x : V) :
    Module.finrank ℚ (ratGramSpace G x) = 12 := by
  have h :
      Module.finrank ℚ (ratGramSpace G x) +
          Module.finrank ℚ (rationalGramKernel G x) =
        Module.finrank ℚ (SecondSubconstituent G x → ℚ) :=
    (rationalGramKernel G x).finrank_quotient_add_finrank
  rw [rationalGramKernel_finrank G hG x, Module.finrank_pi ℚ,
    secondSubconstituent_card G hG x] at h
  omega

/-! ### The comparison map -/

theorem localGramMatrixRat_mulVec_cast (x : V)
    (z : SecondSubconstituent G x → ℤ) :
    localGramMatrixRat G x *ᵥ (fun B => (z B : ℚ)) =
      fun B => ((localGramMatrix G x *ᵥ z) B : ℚ) := by
  funext B
  show (∑ C, ((localGramMatrix G x B C : ℤ) : ℚ) * ((z C : ℤ) : ℚ)) =
    ((∑ C, localGramMatrix G x B C * z C : ℤ) : ℚ)
  push_cast
  rfl

/-- The comparison map on coordinate vectors. -/
def toRatSpaceOnPi (x : V) :
    (SecondSubconstituent G x → ℤ) →ₗ[ℤ] ratGramSpace G x :=
  ((rationalGramKernel G x).mkQ.restrictScalars ℤ).comp
    (integerToRationalVectors G x)

theorem toRatSpaceOnPi_apply (x : V) (z : SecondSubconstituent G x → ℤ) :
    toRatSpaceOnPi G x z = Submodule.Quotient.mk (fun B => (z B : ℚ)) := rfl

theorem ker_toRatSpaceOnPi (x : V) :
    LinearMap.ker (toRatSpaceOnPi G x) = integralGramRelations G x := by
  ext z
  rw [← integralGramKernel_eq_relations]
  simp only [LinearMap.mem_ker, toRatSpaceOnPi_apply, Submodule.Quotient.mk_eq_zero,
    integralGramKernel, Matrix.mulVecLin_apply]
  constructor
  · intro hz
    have hzero : localGramMatrixRat G x *ᵥ (fun B => (z B : ℚ)) = 0 := hz
    rw [localGramMatrixRat_mulVec_cast] at hzero
    funext B
    have hB := congrFun hzero B
    simp only [Pi.zero_apply, Int.cast_eq_zero] at hB
    simpa using hB
  · intro hz
    show localGramMatrixRat G x *ᵥ (fun B => (z B : ℚ)) = 0
    rw [localGramMatrixRat_mulVec_cast]
    funext B
    have hB := congrFun hz B
    simp only [Pi.zero_apply] at hB
    simp [hB]

/-- The comparison map from the integral Gram lattice to the rational Gram
space. -/
def toRatSpace (x : V) :
    IntegralGramLattice G x →ₗ[ℤ] ratGramSpace G x :=
  Submodule.liftQ (integralGramRelations G x) (toRatSpaceOnPi G x)
    (le_of_eq (ker_toRatSpaceOnPi G x).symm)

@[simp]
theorem toRatSpace_mk (x : V) (z : SecondSubconstituent G x → ℤ) :
    toRatSpace G x (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (fun B => (z B : ℚ)) := rfl

theorem toRatSpace_injective (x : V) : Function.Injective (toRatSpace G x) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq (ker_toRatSpaceOnPi G x))

theorem toRatSpace_pairing (x : V) (a b : IntegralGramLattice G x) :
    ratGramForm G x (toRatSpace G x a) (toRatSpace G x b) =
      (integralGramPairing G x a b : ℚ) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  have hint :
      integralGramPairing G x (Submodule.Quotient.mk z) (Submodule.Quotient.mk w) =
        z ⬝ᵥ (localGramMatrix G x *ᵥ w) :=
    Matrix.toBilin'_apply' _ _ _
  rw [toRatSpace_mk, toRatSpace_mk, ratGramForm_mk, localGramMatrixRat_mulVec_cast,
    hint]
  show (∑ C, ((z C : ℤ) : ℚ) * (((localGramMatrix G x *ᵥ w) C : ℤ) : ℚ)) =
    ((∑ C, z C * (localGramMatrix G x *ᵥ w) C : ℤ) : ℚ)
  push_cast
  rfl

@[simp]
theorem toRatSpace_generator (x : V) (B : SecondSubconstituent G x) :
    toRatSpace G x (integralGramGenerator G x B) =
      Submodule.Quotient.mk (Pi.single B (1 : ℚ)) := by
  rw [integralGramGenerator, toRatSpace_mk]
  congr 1
  funext C
  by_cases h : C = B <;> simp [h]

/-! ### The image lattice -/

/-- The image of the integral Gram lattice inside the rational Gram space. -/
def gramLattice (x : V) : Submodule ℤ (ratGramSpace G x) :=
  LinearMap.range (toRatSpace G x)

theorem toRatSpace_mem_gramLattice (x : V) (a : IntegralGramLattice G x) :
    toRatSpace G x a ∈ gramLattice G x :=
  LinearMap.mem_range_self _ _

theorem gramLattice_span_top (x : V) :
    Submodule.span ℚ ((gramLattice G x : Submodule ℤ (ratGramSpace G x)) :
        Set (ratGramSpace G x)) = ⊤ := by
  classical
  set b := Pi.basisFun ℚ (SecondSubconstituent G x) with hb
  have hrange :
      Set.range ((rationalGramKernel G x).mkQ ∘ b) ⊆
        ((gramLattice G x : Submodule ℤ (ratGramSpace G x)) :
          Set (ratGramSpace G x)) := by
    rintro _ ⟨B, rfl⟩
    refine ⟨integralGramGenerator G x B, ?_⟩
    rw [toRatSpace_generator]
    simp [hb, Pi.basisFun_apply]
  have htop :
      Submodule.span ℚ (Set.range ((rationalGramKernel G x).mkQ ∘ b)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      LinearMap.range_eq_top]
    exact Submodule.mkQ_surjective _
  refine top_unique ?_
  rw [← htop]
  exact Submodule.span_mono hrange

theorem gramLattice_fg (x : V) : (gramLattice G x).FG := by
  haveI : Module.Finite ℤ (IntegralGramLattice G x) :=
    Module.Finite.of_surjective (integralGramRelations G x).mkQ
      (Submodule.mkQ_surjective _)
  exact Submodule.fg_range (toRatSpace G x)

theorem gramLattice_isLattice (x : V) :
    Lattice.IsLattice ℚ (gramLattice G x) :=
  ⟨gramLattice_fg G x, gramLattice_span_top G x⟩

end SRG266
