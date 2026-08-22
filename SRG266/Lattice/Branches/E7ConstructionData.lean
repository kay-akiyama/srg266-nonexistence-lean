/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Branches.E7ConstructionBlockData
import SRG266.Hosts.E7ComponentEnumerationCore
import SRG266.Hosts.E7CanonicalCoordinates
import SRG266.Hosts.TuplePermutation

/-!
# Normalized construction data for the E7 branch

This module performs the arithmetic normalization of a pure
`(E₇ ⊕ E₇)⁺` core model.  The resulting finite data and invariants are
packaged for the shell-realization construction in
`SRG266.Lattice.Branches.E7E7`.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

set_option maxRecDepth 40000

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {G}

/-- Normalized block data extracted from a pure E7 core model. -/
structure E7BranchConstructionData {x : V}
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (M : PureCoreModel E c e7e7PlusGram) where
  Y : SecondSubconstituent G x → Bool → Fin 8 → ℤ
  D : Bool → Fin 8 → ℤ
  par : Bool → ℕ
  a : Bool → Fin 8 → ℤ
  n : Bool → ℤ
  σ : Bool → Equiv.Perm (Fin 8)
  p : Bool → Array ℤ
  Y_eq : ∀ B side i, Y B side i = e7e7PlusBlock side (M.generator B) i
  D_eq : ∀ side i, D side i = e7e7PlusBlock side M.centroid i
  D_five : ∀ side i, (5 : ℤ) ∣ D side i
  subconstituent_card :
    (Finset.univ : Finset (SecondSubconstituent G x)).card = 220
  Y_minimal : ∀ B side, IsE7Minimal (Y B side)
  Y_sq : ∀ B side, ∑ i, (Y B side i) ^ 2 = 24
  D_sum : ∀ side, ∑ i, D side i = 0
  par_cases : ∀ side, par side = 0 ∨ par side = 1
  D_split : ∀ side i, D side i = 2 * (2 * a side i + (par side : ℤ))
  D_sq : ∀ side, ∑ i, (D side i) ^ 2 = 16 * n side
  n_even : ∀ side, (2 : ℤ) ∣ n side
  n_total : n false + n true = 300
  n_le_threeHundred : ∀ side, n side ≤ 300
  a_sum : ∀ side, ∑ i, a side i = e7ComponentTargetSum (par side)
  a_sq : ∀ side, ∑ i, (a side i) ^ 2 = n side + 2 * (par side : ℤ) ^ 2
  a_bound : ∀ side i, -17 ≤ a side i ∧ a side i ≤ 17
  a_special : ∀ side, par side = 1 → ∀ i, a side i ≤ 16
  σ_apply : ∀ side i,
    (e7CanonicalReducedCoordinates (List.ofFn (a side))).getD i.1 0 =
      a side (σ side i)
  p_eq : ∀ side, p side = e7ScaleReducedProfile (par side)
    (e7CanonicalReducedCoordinates (List.ofFn (a side)))

/-- Extract the normalized finite block data before constructing the shell
realization. -/
theorem e7BranchConstructionData_of_pureCoreModel {x : V}
    (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c e7e7PlusGram) :
    Nonempty (E7BranchConstructionData M) := by
  classical
  obtain ⟨B⟩ := e7ConstructionBlockData_of_pureCoreModel hG hc M
  rcases B with ⟨Y, D, par, a, n, hY, hD, hDfive, hcard, hYmin,
    hYsq, hDsum, hpar01, hDa, hn, hneven, htotal, hn300⟩
  have hasum : ∀ side, ∑ i, a side i = e7ComponentTargetSum (par side) := by
    intro side
    have h := hDsum side
    rw [Finset.sum_congr rfl fun i _ => hDa side i] at h
    have hexp : ∑ i, 2 * (2 * a side i + (par side : ℤ)) =
        4 * (∑ i, a side i) + 16 * (par side : ℤ) := by
      rw [Finset.sum_congr rfl fun i _ =>
        show 2 * (2 * a side i + (par side : ℤ)) = 4 * a side i + 2 * (par side : ℤ) by ring,
        Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ]
      norm_num
      ring
    rw [hexp] at h
    rcases hpar01 side with hp | hp
    · rw [hp] at h ⊢
      show ∑ i, a side i = (0 : ℤ)
      push_cast at h
      omega
    · rw [hp] at h ⊢
      show ∑ i, a side i = (-4 : ℤ)
      push_cast at h
      omega
  have hasq : ∀ side, ∑ i, (a side i) ^ 2 = n side + 2 * (par side : ℤ) ^ 2 := by
    intro side
    have h := hn side
    rw [Finset.sum_congr rfl fun i _ => by rw [hDa side i]] at h
    have hexp : ∑ i, (2 * (2 * a side i + (par side : ℤ))) ^ 2 =
        16 * (∑ i, (a side i) ^ 2) + (16 * (par side : ℤ)) * (∑ i, a side i) +
          32 * (par side : ℤ) ^ 2 := by
      rw [Finset.sum_congr rfl fun i _ =>
        show (2 * (2 * a side i + (par side : ℤ))) ^ 2 =
          16 * (a side i) ^ 2 + (16 * (par side : ℤ)) * a side i +
            4 * (par side : ℤ) ^ 2 by ring,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ]
      norm_num
      ring
    rw [hexp, hasum side] at h
    rcases hpar01 side with hp | hp
    · rw [hp] at h ⊢
      push_cast at h ⊢
      simp only [e7ComponentTargetSum] at h
      norm_num at h
      omega
    · rw [hp] at h ⊢
      push_cast at h ⊢
      simp only [e7ComponentTargetSum] at h
      norm_num at h
      omega
  have hysq : ∀ side, ∑ i, (2 * a side i + (par side : ℤ)) ^ 2 = 4 * n side := by
    intro side
    have h := hn side
    rw [Finset.sum_congr rfl fun i _ => by rw [hDa side i]] at h
    have hexp : ∑ i, (2 * (2 * a side i + (par side : ℤ))) ^ 2 =
        4 * ∑ i, (2 * a side i + (par side : ℤ)) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexp] at h
    omega
  have hzbound : ∀ side i, -34 ≤ 2 * a side i + (par side : ℤ) ∧
      2 * a side i + (par side : ℤ) ≤ 34 := by
    intro side i
    have hle : (2 * a side i + (par side : ℤ)) ^ 2 ≤
        ∑ j, (2 * a side j + (par side : ℤ)) ^ 2 :=
      Finset.single_le_sum (f := fun j => (2 * a side j + (par side : ℤ)) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hysq side] at hle
    have h300 := hn300 side
    constructor <;> nlinarith [hle, h300]
  have habound : ∀ side i, -17 ≤ a side i ∧ a side i ≤ 17 := by
    intro side i
    have h := hzbound side i
    rcases hpar01 side with hp | hp <;> rw [hp] at h <;> push_cast at h <;> omega
  have haspecial : ∀ side, par side = 1 → ∀ i, a side i ≤ 16 := by
    intro side hp i
    have h := hzbound side i
    rw [hp] at h
    push_cast at h
    omega
  -- the canonical reordering of each factor
  have hcanon : ∀ side, ∃ σ : Equiv.Perm (Fin 8), ∀ i : Fin 8,
      (e7CanonicalReducedCoordinates (List.ofFn (a side))).getD i.1 0 = a side (σ i) := by
    intro side
    have hperm := e7CanonicalReducedCoordinates_perm (List.ofFn (a side))
    have hlen : (e7CanonicalReducedCoordinates (List.ofFn (a side))).length = 8 :=
      hperm.length_eq.trans (by simp)
    have hofFn : List.ofFn (fun i : Fin 8 =>
        (e7CanonicalReducedCoordinates (List.ofFn (a side))).getD i.1 0) =
          e7CanonicalReducedCoordinates (List.ofFn (a side)) := by
      refine List.ext_getElem (by rw [List.length_ofFn, hlen]) fun i h1 h2 => ?_
      rw [List.getElem_ofFn]
      exact List.getD_eq_getElem _ 0 h2
    obtain ⟨σ, hσ⟩ := exists_fin_perm_comp_ofFn_perm
      (f := fun i : Fin 8 => (e7CanonicalReducedCoordinates (List.ofFn (a side))).getD i.1 0)
      (g := a side) (by rw [hofFn]; exact hperm)
    exact ⟨σ, fun i => (hσ i).symm⟩
  choose σ hσ using hcanon
  -- the two enumerated profiles
  obtain ⟨p, hp⟩ : ∃ p : Bool → Array ℤ, ∀ side, p side =
      e7ScaleReducedProfile (par side)
        (e7CanonicalReducedCoordinates (List.ofFn (a side))) := ⟨_, fun _ => rfl⟩
  exact ⟨{
    Y := Y
    D := D
    par := par
    a := a
    n := n
    σ := σ
    p := p
    Y_eq := hY
    D_eq := hD
    D_five := hDfive
    subconstituent_card := hcard
    Y_minimal := hYmin
    Y_sq := hYsq
    D_sum := hDsum
    par_cases := hpar01
    D_split := hDa
    D_sq := hn
    n_even := hneven
    n_total := htotal
    n_le_threeHundred := hn300
    a_sum := hasum
    a_sq := hasq
    a_bound := habound
    a_special := haspecial
    σ_apply := hσ
    p_eq := hp }⟩

end Lattice
end SRG266
