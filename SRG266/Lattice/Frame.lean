/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.KernelReduction
import SRG266.Lattice.PositiveDefinite

/-!
# The frame identity and the denominator bound `225 · Λ^∨ ⊆ Λ`

Let `Λ = gramLattice G x` be the image of the integral Gram lattice inside the
rational Gram space of a hypothetical `srg(266, 45, 0, 9)`, and let `g_B` be its
distinguished generators.  Two repository facts drive this file:

* `localGramMatrix_sq`: `L * L = 45 • L + 90 • J`;
* `exists_integral_centroid`: there is a lattice vector `c` with `11 • c = ∑ g_B`,
  and it satisfies `⟨c, g_B⟩ = 15`.

Together they say that the Gram vectors form a *frame*:

`∑_C ⟨g_B, g_C⟩ • g_C = 45 • g_B + 6 • c`  (`gram_frame_identity`),

an identity in `Λ` itself rather than merely a numerical identity among the
pairings.  Applying it to a dual vector `y ∈ Λ^∨` and solving the resulting
linear system yields the *denominator bound*

`225 • y ∈ Λ`  (`gram_dual_denominator`),

so that `Λ ⊆ Λ^∨` with `Λ^∨/Λ` a finite abelian group of exponent dividing
`225 = 3² · 5²`; in particular its order is a `{3, 5}`-number.  The finiteness is
recorded as `gramLattice_dual_quotient_finite`, which is what turns the index of
an intermediate integral overlattice into a bounded `ℕ`-valued invariant.

The bound is exactly what removes the `ℚ_p`-classification machinery from the
rank-15 embedding argument: only the primes `3` and `5` can occur in the
discriminant group, and there are finitely many possibilities for each.
-/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Scalar bookkeeping for the rational form

`ratGramSpace G x` is a `ℚ`-vector space, but a lattice inside it is a
`ℤ`-submodule, so integer scalars are unavoidable.  These two lemmas move a
`ℤ`-scalar out of either slot of the form and turn it into an honest rational
multiplication. -/

theorem ratGramForm_zsmul_right (x : V) (v w : ratGramSpace G x) (k : ℤ) :
    ratGramForm G x v (k • w) = (k : ℚ) * ratGramForm G x v w := by
  rw [map_zsmul, zsmul_eq_mul]

theorem ratGramForm_zsmul_left (x : V) (v w : ratGramSpace G x) (k : ℤ) :
    ratGramForm G x (k • v) w = (k : ℚ) * ratGramForm G x v w := by
  calc ratGramForm G x (k • v) w
      = ratGramForm G x w (k • v) := (ratGramForm_isSymm G x).eq _ _
    _ = (k : ℚ) * ratGramForm G x w v := ratGramForm_zsmul_right G x w v k
    _ = (k : ℚ) * ratGramForm G x v w := by rw [(ratGramForm_isSymm G x).eq w v]

/-! ### The distinguished generators span the rational Gram space -/

/-- Every vector of the rational Gram space is a rational combination of the
images of the distinguished generators. -/
theorem ratGramSpace_mk_eq_sum_smul_generator (x : V)
    (a : SecondSubconstituent G x → ℚ) :
    (Submodule.Quotient.mk a : ratGramSpace G x) =
      ∑ B, a B • toRatSpace G x (integralGramGenerator G x B) := by
  have hsum : (∑ B, a B • Pi.single B (1 : ℚ)) = a := by
    funext C
    simp [Pi.single_apply, Finset.sum_ite_eq]
  calc (Submodule.Quotient.mk a : ratGramSpace G x)
      = (rationalGramKernel G x).mkQ (∑ B, a B • Pi.single B (1 : ℚ)) := by
        rw [hsum]; rfl
    _ = ∑ B, a B • toRatSpace G x (integralGramGenerator G x B) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [map_smul, toRatSpace_generator]
        rfl

/-- A rational vector orthogonal to every distinguished generator is zero. -/
theorem eq_zero_of_ratPairing_generators_eq_zero (hG : IsHypothetical G) (x : V)
    (v : ratGramSpace G x)
    (h : ∀ B, ratGramForm G x (toRatSpace G x (integralGramGenerator G x B)) v = 0) :
    v = 0 := by
  refine (ratGramForm_nondegenerate G hG x).2 v fun w => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [ratGramSpace_mk_eq_sum_smul_generator, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun B _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, h B, mul_zero]

/-! ### The frame identity -/

/-- **Lemma F (frame identity).**  The distinguished Gram vectors satisfy
`∑_C ⟨g_B, g_C⟩ • g_C = 45 • g_B + 6 • c` for any integral centroid `c`.  This is
an identity in the lattice, not merely between pairings: both sides have the
same inner product with every generator, and the form is positive definite. -/
theorem gram_frame_identity (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) :
    ∑ C, localGramMatrix G x B C • integralGramGenerator G x C =
      (45 : ℤ) • integralGramGenerator G x B + (6 : ℤ) • c := by
  refine sub_eq_zero.mp (eq_zero_of_pairing_generators_eq_zero G hG x _ fun D => ?_)
  have hlhs :
      integralGramPairing G x
          (∑ C, localGramMatrix G x B C • integralGramGenerator G x C)
          (integralGramGenerator G x D) =
        ∑ C, localGramMatrix G x B C * localGramMatrix G x C D := by
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul,
      integralGramPairing_generator_generator]
  have hrhs :
      integralGramPairing G x
          ((45 : ℤ) • integralGramGenerator G x B + (6 : ℤ) • c)
          (integralGramGenerator G x D) =
        45 * localGramMatrix G x B D + 6 * 15 := by
    rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      map_smul, LinearMap.smul_apply, smul_eq_mul,
      integralGramPairing_generator_generator,
      integral_centroid_pairing_generator G hG x c hc D]
  have hmul :
      (∑ C, localGramMatrix G x B C * localGramMatrix G x C D) =
        45 * localGramMatrix G x B D + 90 := by
    rw [← Matrix.mul_apply, localGramMatrix_sq_apply G hG x B D]
  rw [map_sub, LinearMap.sub_apply, hlhs, hrhs, hmul]
  ring

/-- The frame identity transported to the rational Gram space. -/
theorem ratGram_frame_identity (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) :
    ∑ C, (localGramMatrix G x B C) •
        toRatSpace G x (integralGramGenerator G x C) =
      (45 : ℤ) • toRatSpace G x (integralGramGenerator G x B) +
        (6 : ℤ) • toRatSpace G x c := by
  have h := congrArg (toRatSpace G x) (gram_frame_identity G hG x c hc B)
  rw [map_add, map_smul, map_smul, map_sum] at h
  rw [← h]
  exact Finset.sum_congr rfl fun C _ => (map_smul _ _ _).symm

/-! ### Integrality of the lattice -/

/-- The image lattice is integral for the rational Gram form. -/
theorem gramLattice_isIntegral (x : V) :
    Lattice.IsIntegral (ratGramForm G x) (gramLattice G x) := by
  rw [Lattice.isIntegral_iff_forall]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [toRatSpace_pairing]
  exact Submodule.mem_one.mpr ⟨integralGramPairing G x a b, by simp⟩

/-- `Λ ⊆ Λ^∨`. -/
theorem gramLattice_le_dual (x : V) :
    gramLattice G x ≤ (ratGramForm G x).dualSubmodule (gramLattice G x) :=
  gramLattice_isIntegral G x

/-- The dual lattice is again a lattice. -/
theorem gramLattice_dual_isLattice (hG : IsHypothetical G) (x : V) :
    Lattice.IsLattice ℚ ((ratGramForm G x).dualSubmodule (gramLattice G x)) :=
  Lattice.dual_isLattice (ratGramForm G x) (gramLattice_isLattice G x)
    (ratGramForm_nondegenerate G hG x)

/-! ### The denominator bound -/

/-- **Lemma D (denominator bound).**  Every vector of the dual lattice has
denominator dividing `225`: if `⟨y, λ⟩ ∈ ℤ` for all `λ ∈ Λ`, then `225 y ∈ Λ`.

The proof solves the linear system produced by the frame identity.  Writing
`n_B = ⟨y, g_B⟩ ∈ ℤ` and `m = ⟨y, c⟩ ∈ ℤ`, the lattice vector
`z = ∑_B n_B • g_B` satisfies `⟨z, g_D⟩ = 45 n_D + 6m`, whence
`⟨5 z - 2m c, g_D⟩ = 225 n_D = ⟨225 y, g_D⟩` for every `D`.  The generators span
the space and the form is nondegenerate, so `225 y = 5 z - 2m c ∈ Λ`. -/
theorem gram_dual_denominator (hG : IsHypothetical G) (x : V) :
    ∀ y ∈ (ratGramForm G x).dualSubmodule (gramLattice G x),
      (225 : ℤ) • y ∈ gramLattice G x := by
  classical
  intro y hy
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  -- the integer coordinates of `y`
  have hint : ∀ a : IntegralGramLattice G x,
      ∃ k : ℤ, (k : ℚ) = ratGramForm G x (toRatSpace G x a) y := by
    intro a
    obtain ⟨k, hk⟩ := Submodule.mem_one.mp (hy _ (toRatSpace_mem_gramLattice G x a))
    refine ⟨k, ?_⟩
    rw [(ratGramForm_isSymm G x).eq]
    simpa using hk
  choose n hn using fun B => hint (integralGramGenerator G x B)
  obtain ⟨m, hm⟩ := hint c
  set z : IntegralGramLattice G x := ∑ B, n B • integralGramGenerator G x B with hzdef
  -- the frame identity, paired against `y`
  have hrow : ∀ D, (∑ B, (localGramMatrix G x D B : ℚ) * (n B : ℚ)) =
      45 * (n D : ℚ) + 6 * (m : ℚ) := by
    intro D
    have hpair := congrArg (fun u => ratGramForm G x u y)
      (ratGram_frame_identity G hG x c hc D)
    simp only [map_sum, LinearMap.sum_apply, map_add, LinearMap.add_apply,
      ratGramForm_zsmul_left] at hpair
    simp only [← hn, ← hm] at hpair
    rw [hpair]
    norm_num
  -- the pairings of the auxiliary lattice vector `z`
  have hz : ∀ D, ratGramForm G x (toRatSpace G x (integralGramGenerator G x D))
      (toRatSpace G x z) = 45 * (n D : ℚ) + 6 * (m : ℚ) := by
    intro D
    have hcast :
        integralGramPairing G x (integralGramGenerator G x D)
            (∑ B, n B • integralGramGenerator G x B) =
          ∑ B, localGramMatrix G x D B * n B := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [map_smul, smul_eq_mul, integralGramPairing_generator_generator]
      ring
    rw [toRatSpace_pairing, hzdef, hcast]
    push_cast
    exact hrow D
  -- the pairings of the centroid
  have hcent : ∀ D, ratGramForm G x (toRatSpace G x (integralGramGenerator G x D))
      (toRatSpace G x c) = 15 := by
    intro D
    rw [toRatSpace_pairing,
      (integralGramPairing_isSymm G x).eq (integralGramGenerator G x D) c,
      integral_centroid_pairing_generator G hG x c hc D]
    norm_num
  -- the difference vanishes against every generator, hence vanishes
  refine ⟨(5 : ℤ) • z - (2 * m : ℤ) • c, ?_⟩
  have hkey : (225 : ℤ) • y -
      toRatSpace G x ((5 : ℤ) • z - (2 * m : ℤ) • c) = 0 := by
    refine eq_zero_of_ratPairing_generators_eq_zero G hG x _ fun D => ?_
    have hsplit : toRatSpace G x ((5 : ℤ) • z - (2 * m : ℤ) • c) =
        (5 : ℤ) • toRatSpace G x z - (2 * m : ℤ) • toRatSpace G x c := by
      rw [map_sub, map_smul, map_smul]
    rw [hsplit, map_sub, map_sub]
    simp only [ratGramForm_zsmul_right]
    rw [hz D, hcent D, ← hn D]
    push_cast
    ring
  exact (sub_eq_zero.mp hkey).symm

/-! ### Finiteness of the dual quotient -/

/-- The dual quotient `Λ^∨/Λ` of a hypothetical `srg(266, 45, 0, 9)`. -/
abbrev gramDualQuotient (x : V) :=
  (ratGramForm G x).dualSubmodule (gramLattice G x) ⧸
    (gramLattice G x).comap
      ((ratGramForm G x).dualSubmodule (gramLattice G x)).subtype

/-- **Corollary D1, exponent.**  The dual quotient is annihilated by
`225 = 3² · 5²`; in particular only the primes `3` and `5` occur in it. -/
theorem gramDualQuotient_nsmul_eq_zero (hG : IsHypothetical G) (x : V)
    (q : gramDualQuotient G x) : (225 : ℕ) • q = 0 :=
  Lattice.quotient_nsmul_eq_zero
    (fun w hw => by simpa using gram_dual_denominator G hG x w hw) q

/-- **Corollary D1, finiteness.**  The dual quotient `Λ^∨/Λ` is a finite abelian
group. -/
theorem gramLattice_dual_quotient_finite (hG : IsHypothetical G) (x : V) :
    Finite (gramDualQuotient G x) :=
  Lattice.finite_quotient_of_nsmul_le
    (gramLattice_dual_isLattice G hG x).fg (n := 225)
    (fun w hw => by simpa using gram_dual_denominator G hG x w hw)

end SRG266
