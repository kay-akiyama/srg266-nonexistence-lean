/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Branches.E7ConstructionData
import SRG266.Lattice.Branches.E7PayloadData

/-! # Lightweight enumeration witnesses for E7 payload profiles -/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def enumerationWitness_of_constructionData {x : V}
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    {M : PureCoreModel E c e7e7PlusGram}
    (C : E7BranchConstructionData M) :
    ∀ side, E7ComponentEnumerationWitness (C.p side) := by
  classical
  rcases C with ⟨Y, D, par, a, n, σ, p, hY, hD, hDfive, hcard,
    hYmin, hYsq, hDsum, hpar01, hDa, hn, hneven, htotal, hn300,
    hasum, hasq, habound, haspecial, hσ, hp⟩
  intro side
  have hbounds : ∀ z ∈ List.ofFn (a side), -17 ≤ z ∧ z ≤ 17 :=
    List.forall_mem_ofFn_iff.mpr (habound side)
  have hsum : (List.ofFn (a side)).sum = e7ComponentTargetSum (par side) := by
    rw [List.sum_ofFn]
    exact hasum side
  have hsqle : ((List.ofFn (a side)).map (fun z : ℤ => z * z)).sum ≤
      e7ComponentTargetSq (par side) := by
    have hmap : ((List.ofFn (a side)).map (fun z : ℤ => z * z)).sum =
        ∑ i, (a side i) ^ 2 := by
      rw [List.map_ofFn, List.sum_ofFn]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [Function.comp_apply]
        ring
    have h300 := hn300 side
    rw [hmap, hasq side]
    rcases hpar01 side with hp1 | hp1
    · rw [hp1]
      show n side + 2 * ((0 : ℕ) : ℤ) ^ 2 ≤ ((300 : ℕ) : ℤ)
      push_cast
      omega
    · rw [hp1]
      show n side + 2 * ((1 : ℕ) : ℤ) ^ 2 ≤ ((302 : ℕ) : ℤ)
      push_cast
      omega
  have hspecial : par side = 1 → (List.ofFn (a side)).count 17 = 0 := by
    intro hp1
    refine List.count_eq_zero.mpr fun hcontra => ?_
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hcontra
    have := haspecial side hp1 i
    omega
  exact {
    parity := par side
    source := List.ofFn (a side)
    canonical := e7CanonicalReducedCoordinates (List.ofFn (a side))
    parity_cases := hpar01 side
    source_length := by simp
    source_bounds := hbounds
    source_sum := hsum
    source_sq := hsqle
    source_special := hspecial
    canonical_perm :=
      e7CanonicalReducedCoordinates_perm (List.ofFn (a side))
    canonical_sorted :=
      e7CanonicalReducedCoordinates_pairwise (List.ofFn (a side))
    profile_eq := hp side }

end Lattice
end SRG266
