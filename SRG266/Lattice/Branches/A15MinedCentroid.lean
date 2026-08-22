/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Branches.PureCore
import SRG266.Lattice.Hosts.A15Plus
import SRG266.Hosts.A15MinedNormProfile

/-!
# The divided centroid of the `A₁₅⁺` branch

This module isolates the congruence and norm argument which sends the
geometric centroid to the 17-profile mined norm classification.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every entry of the scaled centroid `4c` is a multiple of ten. -/
theorem a15Plus_centroid_scaledCoordinate_ten_dvd {x : V}
    (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c a15PlusGram) (i : Fin 16) :
    (10 : ℤ) ∣ Matrix.vecMul M.centroid a15PlusCoords i := by
  have hfive : (5 : ℤ) ∣ Matrix.vecMul M.centroid a15PlusCoords i :=
    M.centroid_vecMul_five_dvd hG hc a15PlusGramInv a15PlusGram_isSymm
      a15PlusGram_mul_inv a15PlusCoords i
  have hmem := a15Plus_vecMul_mem M.centroid
  obtain ⟨r, hr, hcong⟩ := hmem.residue_normalised
  have hr02 : r = 0 ∨ r = 2 :=
    a15Plus_residue_of_even_norm M.centroid 300 ⟨150, by norm_num⟩
      (M.centroid_norm hG hc) hr hcong
  have heven : (2 : ℤ) ∣ Matrix.vecMul M.centroid a15PlusCoords i := by
    rcases hcong i with ⟨s, hs⟩
    rcases hr02 with rfl | rfl
    · refine ⟨2 * s, ?_⟩
      omega
    · refine ⟨1 + 2 * s, ?_⟩
      omega
  simpa using (show IsCoprime (5 : ℤ) 2 by norm_num).mul_dvd hfive heven

/-- After division by ten, the centroid has sum zero, squared norm 48, and
common parity. -/
theorem a15Plus_centroid_smallProfile {x : V}
    (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c a15PlusGram) :
    ∃ z : Fin 16 → ℤ,
      (∀ i, Matrix.vecMul M.centroid a15PlusCoords i = 10 * z i) ∧
      (∑ i, z i = 0) ∧
      (∑ i, (z i) ^ 2 = 48) ∧
      (∀ i, z i % 2 = z 0 % 2) := by
  classical
  choose z hz using fun i => a15Plus_centroid_scaledCoordinate_ten_dvd hG hc M i
  refine ⟨z, hz, ?_, ?_, ?_⟩
  · have hsum := (a15Plus_vecMul_mem M.centroid).1
    rw [Finset.sum_congr rfl fun i _ => hz i, ← Finset.mul_sum] at hsum
    omega
  · have hsq :=
      sum_sq_vecMul_coords a15PlusGram a15PlusCoords 4 a15PlusCoords_gram M.centroid
    rw [M.centroid_norm hG hc,
      Finset.sum_congr rfl fun i _ => by rw [hz i]] at hsq
    have hexp : ∑ i, (10 * z i) ^ 2 = 100 * ∑ i, (z i) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexp] at hsq
    omega
  · obtain ⟨r, hr⟩ := (a15Plus_vecMul_mem M.centroid).2
    intro i
    rcases hr i with ⟨s, hs⟩
    rcases hr 0 with ⟨t, ht⟩
    have hzi := hz i
    have hz0 := hz 0
    omega

/-- The canonically reordered divided centroid is one of the 17 explicitly
computed norm profiles. -/
theorem a15Plus_centroid_minedNormProfile {x : V}
    (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c a15PlusGram) :
    ∃ z : Fin 16 → ℤ,
      (∀ i, Matrix.vecMul M.centroid a15PlusCoords i = 10 * z i) ∧
      a15SmallCanonicalCoordinates (List.ofFn z) ∈ a15MinedNormProfiles := by
  classical
  obtain ⟨z, hz, hzsum, hzsq, hzpar⟩ := a15Plus_centroid_smallProfile hG hc M
  refine ⟨z, hz, ?_⟩
  have hzbound : ∀ i, -6 ≤ z i ∧ z i ≤ 6 := by
    intro i
    have hle : z i ^ 2 ≤ ∑ j, (z j) ^ 2 :=
      Finset.single_le_sum (f := fun j => (z j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hzsq] at hle
    constructor <;> nlinarith
  have hlength : (List.ofFn z).length = 16 := by simp
  have hbounds : ∀ q ∈ List.ofFn z, -6 ≤ q ∧ q ≤ 6 :=
    List.forall_mem_ofFn_iff.mpr hzbound
  have hsum : (List.ofFn z).sum = 0 := by
    rw [List.sum_ofFn]
    exact hzsum
  have hsq : ((List.ofFn z).map (fun q : ℤ => q * q)).sum = 48 := by
    rw [List.map_ofFn, List.sum_ofFn]
    calc
      ∑ i, (Function.comp (fun q : ℤ => q * q) z) i =
          ∑ i, (z i) ^ 2 :=
        Finset.sum_congr rfl fun i _ => by simp [Function.comp_apply, pow_two]
      _ = 48 := hzsq
  have hperm := a15SmallCanonicalCoordinates_perm (List.ofFn z) hbounds
  have hrawParity : ∀ q ∈ List.ofFn z, q % 2 = z 0 % 2 :=
    List.forall_mem_ofFn_iff.mpr hzpar
  have hcanonicalParity :
      ∀ q ∈ a15SmallCanonicalCoordinates (List.ofFn z), q % 2 = z 0 % 2 := by
    intro q hq
    exact hrawParity q (hperm.mem_iff.mp hq)
  have hcanonicalLength :
      (a15SmallCanonicalCoordinates (List.ofFn z)).length = 16 :=
    hperm.length_eq.trans hlength
  have hzeroMem :
      (a15SmallCanonicalCoordinates (List.ofFn z)).getD 0 0 ∈
        a15SmallCanonicalCoordinates (List.ofFn z) := by
    cases hcanonical : a15SmallCanonicalCoordinates (List.ofFn z) with
    | nil =>
        rw [hcanonical] at hcanonicalLength
        simp at hcanonicalLength
    | cons q qs =>
        simp
  have hparity :
      a15SmallCommonParity
          (a15SmallCanonicalCoordinates (List.ofFn z)) = true :=
    a15SmallCommonParity_of_mod_eq _ (z 0 % 2) hcanonicalParity
      (hcanonicalParity _ hzeroMem)
  exact a15SmallCanonicalCoordinates_mem_minedNormProfiles_normOnly
    (List.ofFn z) hlength hbounds hsum hsq hparity

end Lattice
end SRG266
