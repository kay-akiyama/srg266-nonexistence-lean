/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.D12Plus
import SRG266.Lattice.Branches.PureCore
import SRG266.Lattice.Hosts.D12PlusZ3

/-!
# The `D₁₂⁺` branch

If the norm-one-free core of the host is `D₁₂⁺`, the pure case of the
trichotomy produces the `d12Plus`
payload of `SRG266.AuditedRank15HostCase` outright: no search, no certificate
and no coordinate normalization.

Three inputs meet here.

* The shell `SRG266.Lattice.d12Plus_norm_three_iff`: every embedded
  generator is a spinor, so its scaled coordinates are a sign vector `ε_B`.
* The integrality lemma `SRG266.Lattice.d12Plus_even_coords_of_even_norm`:
  norms in the half-integral coset are odd, so the centroid — of norm `300` —
  lies in `D₁₂`, with integer coordinates `c_j`.
* The generalized projector bound
  `SRG266.Rank15EmbeddingWitness.directionSquareSum_le'`, evaluated at the
  twelve lattice vectors `2 e_j ∈ D₁₂`.  There `S = 220`, `⟨y, y⟩ = 4` and
  `t = 2 c_j`, so `5 · 220 ≤ 225 · 4 + 2 · (2 c_j)²`, that is `c_j² ≥ 25`.
  Summing, `300 = ⟨c, c⟩ = ∑_j c_j² ≥ 12 · 25 = 300` saturates, so **every**
  `c_j = ±5`.

The sign vector `d_j := c_j / 5` and the eligibility equation
`∑_j d_j ε_{jB} = 6` — read off from `⟨c, v_B⟩ = 15` after clearing the
denominator — are exactly the fields of `SRG266.D12PlusGramRealization`, which
`SRG266.no_d12PlusRealization` already refutes.

The main results are

* `SRG266.Lattice.d12PlusRealization_of_model`, the branch construction;
* `SRG266.Lattice.not_isHostCoreModel_d12Plus`, the branch closed against the
  quasi-symmetric design nonexistence input.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Reading a model coordinate off the pairing -/

variable {G}

/-- **Pairing against a doubled unit vector.**  In `D₁₂⁺` the lattice vector
`2 e_j` pairs with `v` to the `j`-th scaled coordinate of `v`, because the
scale-two model coordinates of `2 e_j` are `4 e_j` and the presentation
multiplies inner products by `4`. -/
theorem d12Plus_toBilin'_doubleUnit (v : Fin 12 → ℤ) (j : Fin 12) :
    Matrix.toBilin' d12PlusGram (fun l => d12PlusDoubleUnit j l) v =
      Matrix.vecMul v d12PlusCoords j := by
  have h := dotProduct_vecMul_coords d12PlusGram d12PlusCoords 2 d12PlusCoords_gram
    (fun l => d12PlusDoubleUnit j l) v
  have hsum : ∑ k, Matrix.vecMul (fun l => d12PlusDoubleUnit j l) d12PlusCoords k *
      Matrix.vecMul v d12PlusCoords k = 4 * Matrix.vecMul v d12PlusCoords j := by
    rw [Finset.sum_eq_single j]
    · rw [d12PlusDoubleUnit_vecMul j j, if_pos rfl]
    · intro k _ hk
      rw [d12PlusDoubleUnit_vecMul j k, if_neg (Ne.symm hk), zero_mul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [dotProduct, hsum] at h
  linarith

/-! ## The branch construction -/

/-- A pure embedding whose core is
presented by the Gram matrix of `D₁₂⁺` realizes the local Gram matrix in the
norm-three spinor shell, with the centroid already normalized to a sign
vector. -/
theorem d12PlusRealization_of_pureCoreModel {x : V} (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c d12PlusGram) :
    Nonempty (D12PlusGramRealization G x) := by
  classical
  -- Every generator is a spinor.
  have hspin : ∀ (B : SecondSubconstituent G x) (j : Fin 12),
      Matrix.vecMul (M.generator B) d12PlusCoords j = 1 ∨
        Matrix.vecMul (M.generator B) d12PlusCoords j = -1 := fun B =>
    (d12Plus_norm_three_iff (M.generator B)).mp (M.generator_norm hG B)
  -- The centroid has even scaled coordinates, so it lies in `D₁₂`.
  have hcentroidNorm : Matrix.toBilin' d12PlusGram M.centroid M.centroid = 2 * 150 := by
    have h := M.centroid_norm hG hc
    linarith
  have heven : ∀ j, (2 : ℤ) ∣ Matrix.vecMul M.centroid d12PlusCoords j :=
    d12Plus_even_coords_of_even_norm M.centroid hcentroidNorm
  choose gamma hgamma using heven
  -- `⟨c, c⟩ = 300` in coordinates.
  have hgammaSum : ∑ j, gamma j ^ 2 = 300 := by
    have h := sum_sq_vecMul_coords d12PlusGram d12PlusCoords 2 d12PlusCoords_gram M.centroid
    rw [M.centroid_norm hG hc] at h
    have hrw : ∑ j, Matrix.vecMul M.centroid d12PlusCoords j ^ 2 =
        4 * ∑ j, gamma j ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hgamma j]; ring
    rw [hrw] at h
    linarith
  -- The number of generators.
  have hcard : (Finset.univ : Finset (SecondSubconstituent G x)).card = 220 := by
    rw [Finset.card_univ]
    exact secondSubconstituent_card G hG x
  -- At `y = 2 e_j`, every centroid coordinate has square at least `25`.
  have hlower : ∀ j ∈ (Finset.univ : Finset (Fin 12)), (25 : ℤ) ≤ gamma j ^ 2 := by
    intro j _
    have hb := M.projector_bound hG hc (fun l => d12PlusDoubleUnit j l)
    have hprofile : ∀ B : SecondSubconstituent G x,
        Matrix.toBilin' d12PlusGram (fun l => d12PlusDoubleUnit j l) (M.generator B) ^ 2 = 1 := by
      intro B
      rw [d12Plus_toBilin'_doubleUnit]
      rcases hspin B j with h | h <;> rw [h] <;> norm_num
    have hS : ∑ B : SecondSubconstituent G x,
        Matrix.toBilin' d12PlusGram (fun l => d12PlusDoubleUnit j l) (M.generator B) ^ 2 =
          220 := by
      rw [Finset.sum_congr rfl fun B _ => hprofile B, Finset.sum_const, hcard]
      norm_num
    have hnorm : Matrix.toBilin' d12PlusGram (fun l => d12PlusDoubleUnit j l)
        (fun l => d12PlusDoubleUnit j l) = 4 := by
      rw [d12Plus_toBilin'_doubleUnit, d12PlusDoubleUnit_vecMul j j, if_pos rfl]
    have htrace : Matrix.toBilin' d12PlusGram (fun l => d12PlusDoubleUnit j l) M.centroid =
        2 * gamma j := by
      rw [d12Plus_toBilin'_doubleUnit, hgamma j]
    rw [hS, hnorm, htrace] at hb
    nlinarith [hb]
  -- Saturation: `∑ c_j² = 300 = 12 · 25` forces equality everywhere.
  have hconst : ∑ _j : Fin 12, (25 : ℤ) = ∑ j, gamma j ^ 2 := by
    rw [hgammaSum, Finset.sum_const, Finset.card_univ]
    norm_num
  have hsq : ∀ j, gamma j ^ 2 = 25 := fun j =>
    ((Finset.sum_eq_sum_iff_of_le hlower).mp hconst j (Finset.mem_univ j)).symm
  have hcases : ∀ j, gamma j = 5 ∨ gamma j = -5 := by
    intro j
    have hfac : (gamma j - 5) * (gamma j + 5) = 0 := by nlinarith [hsq j]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  -- The normalized centroid sign vector.
  set sign : Fin 12 → ℤ := fun j => if gamma j = 5 then 1 else -1 with hsignDef
  have hsignCases : ∀ j, sign j = -1 ∨ sign j = 1 := by
    intro j
    by_cases h : gamma j = 5
    · exact Or.inr (by simp [hsignDef, h])
    · exact Or.inl (by simp [hsignDef, h])
  have hgammaSign : ∀ j, gamma j = 5 * sign j := by
    intro j
    by_cases h : gamma j = 5
    · simp [hsignDef, h]
    · rcases hcases j with h5 | h5
      · exact absurd h5 h
      · simp [hsignDef, h5]
  have hcentroidCoord : ∀ j, Matrix.vecMul M.centroid d12PlusCoords j = 10 * sign j := by
    intro j
    rw [hgamma j, hgammaSign j]
    ring
  refine ⟨{ centroidSign := sign
            spinorSign := fun j B => Matrix.vecMul (M.generator B) d12PlusCoords j
            centroidSign_cases := hsignCases
            spinorSign_cases := fun j B => (hspin B j).symm
            eligibility := ?_
            spinor_gram := ?_ }⟩
  · -- `⟨c, v_B⟩ = 15`, cleared of the denominator two
    intro B
    have h := dotProduct_vecMul_coords d12PlusGram d12PlusCoords 2 d12PlusCoords_gram
      M.centroid (M.generator B)
    rw [M.centroid_generator hG hc, dotProduct] at h
    have hrw : ∑ j, Matrix.vecMul M.centroid d12PlusCoords j *
        Matrix.vecMul (M.generator B) d12PlusCoords j =
          10 * ∑ j, sign j * Matrix.vecMul (M.generator B) d12PlusCoords j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hcentroidCoord j]; ring
    rw [hrw] at h
    linarith
  · -- `⟨v_B, v_C⟩ = L_BC`, cleared of the denominator four
    intro B C
    have h := dotProduct_vecMul_coords d12PlusGram d12PlusCoords 2 d12PlusCoords_gram
      (M.generator B) (M.generator C)
    rw [M.gram B C, dotProduct] at h
    linarith

variable (G)

/-- A pure embedding whose norm-one-free core is modelled by
the Gram matrix of `D₁₂⁺` produces the `d12Plus` payload of
`SRG266.AuditedRank15HostCase`. -/
theorem d12PlusRealization_of_model {x : V} (hG : IsHypothetical G)
    (E : Rank15EmbeddingWitness G x) (hpure : E.NormOneDirectionsOrthogonal G)
    {k : ℕ} {u : Fin k → E.host.carrier} (hu : ∀ i, E.host.pairing (u i) (u i) = 1)
    (hmodel : IsHostCoreModel E.host u d12PlusGram) :
    Nonempty (D12PlusGramRealization G x) := by
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  obtain ⟨M⟩ := PureCoreModel.exists_of_isHostCoreModel E c hc hpure hu hmodel
  exact d12PlusRealization_of_pureCoreModel hG hc M

/-- The realization produced by the `D₁₂⁺` branch is a
one-integral factorization of the local Gram matrix, which
`SRG266.no_d12PlusRealization` refutes. -/
theorem not_isHostCoreModel_d12Plus (hMT : NoQuasiSymmetricDesign56.{u}) {x : V}
    (hG : IsHypothetical G) (E : Rank15EmbeddingWitness G x)
    (hpure : E.NormOneDirectionsOrthogonal G)
    {k : ℕ} {u : Fin k → E.host.carrier} (hu : ∀ i, E.host.pairing (u i) (u i) = 1) :
    ¬IsHostCoreModel E.host u d12PlusGram := fun hmodel =>
  no_d12PlusRealization G hMT hG x (d12PlusRealization_of_model G hG E hpure hu hmodel)

/-- The maximal orthonormal family comes from the norm-one splitting of
`SRG266/Lattice/Core.lean`; the classification hypothesis is applied only to
that family. -/
theorem no_pure_d12PlusCore (hMT : NoQuasiSymmetricDesign56.{u}) {x : V}
    (hG : IsHypothetical G) (E : Rank15EmbeddingWitness G x)
    (hpure : E.NormOneDirectionsOrthogonal G)
    (hclass : ∀ (k : ℕ) (u : Fin k → E.host.carrier),
      (∀ i, E.host.pairing (u i) (u i) = 1) →
      (∀ i j, i ≠ j → E.host.pairing (u i) (u j) = 0) →
      (∀ w : E.host.carrier, (∀ i, E.host.pairing (u i) w = 0) → E.host.pairing w w ≠ 1) →
      IsHostCoreModel E.host u d12PlusGram) :
    False := by
  obtain ⟨k, u, hnorm, horth, hfree, -⟩ := E.host.exists_orthonormal_normOneFree
  exact not_isHostCoreModel_d12Plus G hMT hG E hpure hnorm (hclass k u hnorm horth hfree)

end Lattice
end SRG266
