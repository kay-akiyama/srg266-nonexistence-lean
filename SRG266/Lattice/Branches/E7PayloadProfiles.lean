/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Branches.E7PayloadEnumeration

/-! # Prepared component profiles for E7 payload construction -/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

structure E7PreparedProfiles {x : V}
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    {M : PureCoreModel E c e7e7PlusGram}
    (C : E7BranchConstructionData M) where
  profileD : ∀ side i,
    2 * e7ComponentEnumerationProfile (C.p side) i =
      C.D side (C.σ side i)
  profileFive : ∀ side i,
    (5 : ℤ) ∣ e7ComponentEnumerationProfile (C.p side) i
  enumeration : ∀ side, E7ComponentEnumerationWitness (C.p side)
  profileSum : ∀ side,
    ∑ i, e7ComponentEnumerationProfile (C.p side) i = 0
  profileSq : ∀ side,
    ∑ i, (e7ComponentEnumerationProfile (C.p side) i) ^ 2 =
      4 * C.n side
  profileParity : ∀ side (i j : Fin 8),
    e7ComponentEnumerationProfile (C.p side) i % 2 =
      e7ComponentEnumerationProfile (C.p side) j % 2
  profileSorted : ∀ side,
    (List.ofFn (e7ComponentEnumerationProfile (C.p side))).Pairwise
      (· ≤ ·)

theorem preparedProfiles_of_constructionData {x : V}
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    {M : PureCoreModel E c e7e7PlusGram}
    (C : E7BranchConstructionData M) :
    Nonempty (E7PreparedProfiles C) := by
  classical
  have henumeration := enumerationWitness_of_constructionData C
  rcases C with ⟨Y, D, par, a, n, σ, p, hY, hD, hDfive, hcard,
    hYmin, hYsq, hDsum, hpar01, hDa, hn, hneven, htotal, hn300,
    hasum, hasq, habound, haspecial, hσ, hp⟩
  have hcanonLen : ∀ side,
      (e7CanonicalReducedCoordinates (List.ofFn (a side))).length = 8 := by
    intro side
    exact (e7CanonicalReducedCoordinates_perm (List.ofFn (a side))).length_eq.trans
      (by simp)
  have hprofile : ∀ side i,
      e7ComponentEnumerationProfile (p side) i =
        2 * a side (σ side i) + (par side : ℤ) := by
    intro side i
    rw [hp side,
      e7ComponentEnumerationProfile_scale_apply (par side) _ (hcanonLen side) i, hσ side i]
  have hprofileD : ∀ side i,
      2 * e7ComponentEnumerationProfile (p side) i = D side (σ side i) := by
    intro side i
    rw [hprofile side i, hDa side (σ side i)]
  have hprofileFive : ∀ side i,
      (5 : ℤ) ∣ e7ComponentEnumerationProfile (p side) i := by
    intro side i
    have hdiv : (5 : ℤ) ∣
        2 * e7ComponentEnumerationProfile (p side) i := by
      rw [hprofileD side i]
      exact hDfive side (σ side i)
    exact (show IsCoprime (5 : ℤ) 2 by norm_num).dvd_of_dvd_mul_left hdiv
  have hprofSum : ∀ side,
      ∑ i, e7ComponentEnumerationProfile (p side) i = 0 := by
    intro side
    have h : ∑ i, (2 : ℤ) * e7ComponentEnumerationProfile (p side) i = 0 := by
      rw [Finset.sum_congr rfl fun i _ => hprofileD side i,
        Equiv.sum_comp (σ side) (D side)]
      exact hDsum side
    rw [← Finset.mul_sum] at h
    omega
  have hprofSq : ∀ side,
      ∑ i, (e7ComponentEnumerationProfile (p side) i) ^ 2 = 4 * n side := by
    intro side
    have h : ∑ i, ((2 : ℤ) * e7ComponentEnumerationProfile (p side) i) ^ 2 =
        16 * n side := by
      rw [Finset.sum_congr rfl fun i _ => by rw [hprofileD side i],
        Equiv.sum_comp (σ side) (fun j => (D side j) ^ 2)]
      exact hn side
    have hfour : ∑ i, ((2 : ℤ) * e7ComponentEnumerationProfile (p side) i) ^ 2 =
        4 * ∑ i, (e7ComponentEnumerationProfile (p side) i) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    omega
  have hprofPar : ∀ side (i j : Fin 8),
      e7ComponentEnumerationProfile (p side) i % 2 =
        e7ComponentEnumerationProfile (p side) j % 2 := by
    intro side i j
    rw [hprofile side i, hprofile side j]
    omega
  have hprofileList : ∀ side,
      List.ofFn (e7ComponentEnumerationProfile (p side)) =
        (e7CanonicalReducedCoordinates (List.ofFn (a side))).map
          (fun z => 2 * z + (par side : ℤ)) := by
    intro side
    apply List.ext_getElem
    · rw [List.length_ofFn, List.length_map, hcanonLen side]
    · intro i hleft hright
      have hi : i < 8 := by simpa using hleft
      have hcanonical :
          i < (e7CanonicalReducedCoordinates (List.ofFn (a side))).length := by
        simpa only [List.length_map] using hright
      rw [List.getElem_ofFn]
      simp only [List.getElem_map]
      rw [hp side,
        e7ComponentEnumerationProfile_scale_apply (par side) _
          (hcanonLen side) ⟨i, hi⟩,
        List.getD_eq_getElem _ 0 hcanonical]
  have hprofSorted : ∀ side,
      (List.ofFn (e7ComponentEnumerationProfile (p side))).Pairwise
        (· ≤ ·) := by
    intro side
    rw [hprofileList side]
    exact
      (e7CanonicalReducedCoordinates_pairwise (List.ofFn (a side))).map _
        (fun _ _ h => by omega)
  exact ⟨{
    profileD := hprofileD
    profileFive := hprofileFive
    enumeration := henumeration
    profileSum := hprofSum
    profileSq := hprofSq
    profileParity := hprofPar
    profileSorted := hprofSorted }⟩

end Lattice
end SRG266
