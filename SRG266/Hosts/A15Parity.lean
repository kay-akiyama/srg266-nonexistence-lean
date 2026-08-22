/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The weighted-triple parity obstruction for `A₁₅⁺`

The final two centroid profiles reduce to a weighted triple system on eight
points. If `m T` is the multiplicity of a triple and `λ p` is the total
multiplicity through a pair, the frame equations say that every selected
triple contains pairs of total concurrence 30.

This module derives both global double-counting identities and the final
parity contradiction without importing the Python conclusion.
-/

open scoped BigOperators

namespace SRG266

abbrev A15ParityPoint := Fin 8
abbrev A15ParityPair := {s : Finset A15ParityPoint // s.card = 2}
abbrev A15ParityTriple := {s : Finset A15ParityPoint // s.card = 3}

def a15ParityIncident
    (p : A15ParityPair) (t : A15ParityTriple) : Prop :=
  p.1 ⊆ t.1

instance (p : A15ParityPair) (t : A15ParityTriple) :
    Decidable (a15ParityIncident p t) := by
  unfold a15ParityIncident
  infer_instance

/-- Weighted pair concurrence. -/
def a15ParityConcurrence
    (m : A15ParityTriple → ℕ) (p : A15ParityPair) : ℕ :=
  ∑ t, if a15ParityIncident p t then m t else 0

/-- Sum of the three pair concurrences inside a triple. -/
def a15ParityTriplePairSum
    (m : A15ParityTriple → ℕ) (t : A15ParityTriple) : ℕ :=
  ∑ p, if a15ParityIncident p t then a15ParityConcurrence m p else 0

/-- Number of pairs contained in both triples: three for equal triples, one
for distinct triples sharing two points, and zero otherwise. -/
def a15ParityPairKernel
    (t u : A15ParityTriple) : ℕ :=
  if t = u then 3 else if (t.1 ∩ u.1).card = 2 then 1 else 0

private def a15ParityCommonPairEquiv (t u : A15ParityTriple) :
    {p : A15ParityPair //
      a15ParityIncident p t ∧ a15ParityIncident p u} ≃
      {s : Finset A15ParityPoint //
        s ∈ Finset.powersetCard 2 (t.1 ∩ u.1)} where
  toFun p := ⟨p.1.1, by
    rw [Finset.mem_powersetCard, Finset.subset_inter_iff]
    exact ⟨p.2, p.1.2⟩⟩
  invFun s := ⟨⟨s.1, by
    exact (Finset.mem_powersetCard.mp s.2).2⟩, by
    exact (Finset.subset_inter_iff.mp
      (Finset.mem_powersetCard.mp s.2).1)⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv s := by
    apply Subtype.ext
    rfl

/-- The finite incidence count realizing `a15ParityPairKernel`. -/
theorem a15Parity_common_pair_count
    (t u : A15ParityTriple) :
    (∑ p : A15ParityPair,
      if a15ParityIncident p t ∧ a15ParityIncident p u then 1 else 0) =
      a15ParityPairKernel t u := by
  rw [← Finset.card_filter]
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (a15ParityCommonPairEquiv t u)]
  rw [Fintype.card_coe, Finset.card_powersetCard]
  have hinter : (t.1 ∩ u.1).card ≤ 3 := by
    calc
      (t.1 ∩ u.1).card ≤ t.1.card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = 3 := t.2
  by_cases htu : t = u
  · subst u
    simp [a15ParityPairKernel, t.2]
  · have hne3 : (t.1 ∩ u.1).card ≠ 3 := by
      intro hcard
      have hleft : t.1 ∩ u.1 = t.1 :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
          rw [hcard, t.2])
      have hright : t.1 ∩ u.1 = u.1 :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
          rw [hcard, u.2])
      apply htu
      apply Subtype.ext
      rw [← hleft, hright]
    have hinter2 : (t.1 ∩ u.1).card ≤ 2 := by omega
    interval_cases hcard : (t.1 ∩ u.1).card <;>
      simp [a15ParityPairKernel, htu, hcard]

/-- Expand the three concurrence sums inside a triple as a kernel sum over
all triples. -/
theorem a15ParityTriplePairSum_eq_kernel_sum
    (m : A15ParityTriple → ℕ) (t : A15ParityTriple) :
    a15ParityTriplePairSum m t =
      ∑ u, a15ParityPairKernel t u * m u := by
  unfold a15ParityTriplePairSum a15ParityConcurrence
  calc
    (∑ p : A15ParityPair,
        if a15ParityIncident p t then
          ∑ u : A15ParityTriple,
            if a15ParityIncident p u then m u else 0
        else 0) =
        ∑ p : A15ParityPair, ∑ u : A15ParityTriple,
          if a15ParityIncident p t ∧ a15ParityIncident p u then
            m u
          else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hpt : a15ParityIncident p t
      · simp only [hpt, true_and, ↓reduceIte]
      · simp only [hpt, false_and, ↓reduceIte, Finset.sum_const_zero]
    _ = ∑ u : A15ParityTriple, ∑ p : A15ParityPair,
        if a15ParityIncident p t ∧ a15ParityIncident p u then
          m u
        else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ u : A15ParityTriple,
        a15ParityPairKernel t u * m u := by
      apply Finset.sum_congr rfl
      intro u _
      calc
        (∑ p : A15ParityPair,
            if a15ParityIncident p t ∧ a15ParityIncident p u then
              m u
            else 0) =
            (∑ p : A15ParityPair,
              if a15ParityIncident p t ∧ a15ParityIncident p u then
                1
              else 0) * m u := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p _
          by_cases hboth :
              a15ParityIncident p t ∧ a15ParityIncident p u <;>
            simp [hboth]
        _ = _ := by rw [a15Parity_common_pair_count]

theorem a15Parity_pair_indicator_sum (t : A15ParityTriple) :
    (∑ p : A15ParityPair, if a15ParityIncident p t then 1 else 0) = 3 := by
  simpa [a15ParityPairKernel] using a15Parity_common_pair_count t t

private theorem a15Parity_sum_indicator_const
    (t : A15ParityTriple) (n : ℕ) :
    (∑ p : A15ParityPair, if a15ParityIncident p t then n else 0) =
      n * 3 := by
  calc
    _ = ∑ p : A15ParityPair,
        n * if a15ParityIncident p t then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpt : a15ParityIncident p t <;> simp [hpt]
    _ = n * ∑ p : A15ParityPair,
        if a15ParityIncident p t then 1 else 0 := by
      rw [Finset.mul_sum]
    _ = n * 3 := by rw [a15Parity_pair_indicator_sum]

theorem a15Parity_sum_concurrence
    (m : A15ParityTriple → ℕ) :
    (∑ p, a15ParityConcurrence m p) = 3 * ∑ t, m t := by
  calc
    _ = ∑ p : A15ParityPair, ∑ t : A15ParityTriple,
        if a15ParityIncident p t then m t else 0 := by
      rfl
    _ = ∑ t : A15ParityTriple, ∑ p : A15ParityPair,
        if a15ParityIncident p t then m t else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t : A15ParityTriple, m t * 3 := by
      apply Finset.sum_congr rfl
      intro t ht
      exact a15Parity_sum_indicator_const t (m t)
    _ = 3 * ∑ t, m t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      omega

private theorem a15Parity_concurrence_square
    (m : A15ParityTriple → ℕ) (p : A15ParityPair) :
    a15ParityConcurrence m p ^ 2 =
      ∑ t : A15ParityTriple,
        if a15ParityIncident p t then
          a15ParityConcurrence m p * m t
        else 0 := by
  rw [pow_two, a15ParityConcurrence, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hpt : a15ParityIncident p t <;> simp [hpt]

private theorem a15Parity_sum_incident_product
    (m : A15ParityTriple → ℕ) (t : A15ParityTriple) :
    (∑ p : A15ParityPair,
        if a15ParityIncident p t then
          a15ParityConcurrence m p * m t
        else 0) =
      m t * a15ParityTriplePairSum m t := by
  rw [a15ParityTriplePairSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpt : a15ParityIncident p t <;> simp [hpt, Nat.mul_comm]

theorem a15Parity_sum_concurrence_sq
    (m : A15ParityTriple → ℕ)
    (hframe :
      ∀ t, 0 < m t → a15ParityTriplePairSum m t = 30) :
    (∑ p, a15ParityConcurrence m p ^ 2) =
      30 * ∑ t, m t := by
  calc
    _ = ∑ p : A15ParityPair, ∑ t : A15ParityTriple,
        if a15ParityIncident p t then
          a15ParityConcurrence m p * m t
        else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact a15Parity_concurrence_square m p
    _ = ∑ t : A15ParityTriple, ∑ p : A15ParityPair,
        if a15ParityIncident p t then
          a15ParityConcurrence m p * m t
        else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t : A15ParityTriple,
        m t * a15ParityTriplePairSum m t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact a15Parity_sum_incident_product m t
    _ = ∑ t : A15ParityTriple, m t * 30 := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hzero : m t = 0
      · simp [hzero]
      · rw [hframe t (Nat.pos_of_ne_zero hzero)]
    _ = 30 * ∑ t, m t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      omega

theorem zmod_two_square (x : ZMod 2) : x ^ 2 = x := by
  fin_cases x <;> rfl

theorem a15Parity_no_weighted_triple_system
    (m : A15ParityTriple → ℕ)
    (htotal : (∑ t, m t) = 55)
    (hframe :
      ∀ t, 0 < m t → a15ParityTriplePairSum m t = 30) :
    False := by
  have hsum :
      (∑ p, a15ParityConcurrence m p) = 165 := by
    rw [a15Parity_sum_concurrence, htotal]
  have hsquare :
      (∑ p, a15ParityConcurrence m p ^ 2) = 1650 := by
    rw [a15Parity_sum_concurrence_sq m hframe, htotal]
  have hsumZ :
      (∑ p, (a15ParityConcurrence m p : ZMod 2)) = (165 : ZMod 2) := by
    simpa only [Nat.cast_sum, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ZMod 2)) hsum
  have hsquareZ :
      (∑ p, (a15ParityConcurrence m p : ZMod 2) ^ 2) =
        (1650 : ZMod 2) := by
    simpa only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ZMod 2)) hsquare
  have heq : (1650 : ZMod 2) = (165 : ZMod 2) := by
    rw [← hsquareZ, ← hsumZ]
    apply Finset.sum_congr rfl
    intro p hp
    rw [zmod_two_square]
  exact (by decide : (1650 : ZMod 2) ≠ (165 : ZMod 2)) heq

end SRG266
