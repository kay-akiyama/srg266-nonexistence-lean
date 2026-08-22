/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Branches.PureCoreModel
import SRG266.Lattice.Hosts.E7E7PlusCore

/-! # Arithmetic prerequisites for the pure E7 branch -/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

set_option maxRecDepth 40000

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {G}

/-- The mined congruence before any `E₇` profile enumeration: every entry of
either scaled centroid block is divisible by five. -/
theorem e7e7Plus_centroid_block_five_dvd {x : V}
    (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c e7e7PlusGram) (side : Bool) (i : Fin 8) :
    (5 : ℤ) ∣ e7e7PlusBlock side M.centroid i := by
  unfold e7e7PlusBlock
  exact M.centroid_vecMul_five_dvd hG hc e7e7PlusGramInv e7e7PlusGram_isSymm
    e7e7PlusGram_mul_inv e7e7PlusCoords (if side then Sum.inr i else Sum.inl i)

/-- After the existing glue-parity step writes a block entry as `2y`, the
actual component coordinate `y` is still divisible by five. -/
theorem e7e7Plus_centroid_halfBlock_five_dvd {x : V}
    (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c e7e7PlusGram) (side : Bool) (i : Fin 8)
    (y : ℤ) (hy : e7e7PlusBlock side M.centroid i = 2 * y) :
    (5 : ℤ) ∣ y := by
  have hfive := e7e7Plus_centroid_block_five_dvd hG hc M side i
  rw [hy] at hfive
  exact (show IsCoprime (5 : ℤ) 2 by norm_num).dvd_of_dvd_mul_left hfive

/-- A small computable replacement for the scalar norm sweep.  A block with
all coordinates divisible by five, the existing even-norm condition, and the
projector bounds can have only one of five norms. -/
theorem e7e7Plus_componentNorm_cases (D : Fin 8 → ℤ) (n : ℤ)
    (hfive : ∀ i, (5 : ℤ) ∣ D i)
    (hsq : ∑ i, (D i) ^ 2 = 16 * n)
    (heven : (2 : ℤ) ∣ n) (hlow : 38 ≤ n) (hhigh : n ≤ 262) :
    n = 50 ∨ n = 100 ∨ n = 150 ∨ n = 200 ∨ n = 250 := by
  have h25sum : (25 : ℤ) ∣ ∑ i, (D i) ^ 2 := by
    exact Finset.dvd_sum fun i _ => by
      rcases hfive i with ⟨q, hq⟩
      refine ⟨q ^ 2, ?_⟩
      rw [hq]
      ring
  rw [hsq] at h25sum
  have h25 : (25 : ℤ) ∣ n :=
    (show IsCoprime (25 : ℤ) 16 by norm_num).dvd_of_dvd_mul_left h25sum
  have h50 : (50 : ℤ) ∣ n := by
    simpa using (show IsCoprime (25 : ℤ) 2 by norm_num).mul_dvd h25 heven
  rcases h50 with ⟨k, hk⟩
  omega

end Lattice
end SRG266

