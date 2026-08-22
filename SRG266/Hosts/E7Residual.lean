/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7ResidualCore
import Mathlib.Tactic

/-!
# Residual `E₇ ⊕ E₇` shell packings

This module introduces the weaker packing structure needed by the first
residual contradiction.  A required Gram configuration selects 220 eligible
shell vectors with multiplicities at most three.  Since its Gram entries are
nonnegative, two selected shell vectors cannot have negative inner product.

The generic component-capacity lemma below excludes any such packing when
the shell is partitioned into at most 36 bipartite negative components, with
at most two vertices on either side of a component.  The concrete
`6g × 6g` component table is supplied and checked in a certificate module.
-/

open scoped BigOperators

namespace SRG266

/-- The part of a required residual shell realization used by negative-edge
capacity arguments. -/
structure E7ShellPacking (d₁ d₂ : Fin 8 → ℤ) where
  multiplicity : E7ResidualEligibleIndex d₁ d₂ → ℕ
  le_three : ∀ w, multiplicity w ≤ 3
  total : ∑ w, multiplicity w = 220
  leftCentroid :
    ∀ i, ∑ w, (multiplicity w : ℤ) * e7Weight4 w.1.1 i =
      110 * d₁ i
  rightCentroid :
    ∀ i, ∑ w, (multiplicity w : ℤ) * e7Weight4 w.1.2 i =
      110 * d₂ i
  twoProfile :
    ∀ u, 0 < multiplicity u →
      (∑ v ∈ Finset.univ.filter
          (fun v => e7ShellInner u.1 v.1 = 2), multiplicity v) +
        3 * multiplicity u = 30
  nonnegative :
    ∀ u v, 0 < multiplicity u → 0 < multiplicity v →
      0 ≤ e7ShellInner u.1 v.1

/-- Apply an affine integral functional to the left centroid equations. -/
theorem E7ShellPacking.left_affine_sum
    {d₁ d₂ : Fin 8 → ℤ} (packing : E7ShellPacking d₁ d₂)
    (q₀ : ℤ) (q : Fin 8 → ℤ) :
    ∑ w, (packing.multiplicity w : ℤ) *
        (q₀ + integerDot q (e7Weight4 w.1.1)) =
      q₀ * 220 + 110 * integerDot q d₁ := by
  calc
    (∑ w, (packing.multiplicity w : ℤ) *
        (q₀ + integerDot q (e7Weight4 w.1.1))) =
        (∑ w, (packing.multiplicity w : ℤ) * q₀) +
          ∑ w, ∑ i, (packing.multiplicity w : ℤ) *
            (q i * e7Weight4 w.1.1 i) := by
      simp only [integerDot]
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ = q₀ * ∑ w, (packing.multiplicity w : ℤ) +
          ∑ i, q i *
            ∑ w, (packing.multiplicity w : ℤ) *
              e7Weight4 w.1.1 i := by
      rw [Finset.sum_comm]
      apply congrArg₂ (· + ·)
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
      · apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
    _ = q₀ * 220 + ∑ i, q i * (110 * d₁ i) := by
      have htotalZ :
          (∑ w, (packing.multiplicity w : ℤ)) = 220 := by
        exact_mod_cast packing.total
      rw [htotalZ]
      apply congrArg (q₀ * 220 + ·)
      apply Finset.sum_congr rfl
      intro i _
      rw [packing.leftCentroid i]
    _ = q₀ * 220 + 110 * integerDot q d₁ := by
      simp only [integerDot]
      rw [Finset.mul_sum]
      apply congrArg (q₀ * 220 + ·)
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Apply an affine integral functional to the right centroid equations. -/
theorem E7ShellPacking.right_affine_sum
    {d₁ d₂ : Fin 8 → ℤ} (packing : E7ShellPacking d₁ d₂)
    (q₀ : ℤ) (q : Fin 8 → ℤ) :
    ∑ w, (packing.multiplicity w : ℤ) *
        (q₀ + integerDot q (e7Weight4 w.1.2)) =
      q₀ * 220 + 110 * integerDot q d₂ := by
  calc
    (∑ w, (packing.multiplicity w : ℤ) *
        (q₀ + integerDot q (e7Weight4 w.1.2))) =
        (∑ w, (packing.multiplicity w : ℤ) * q₀) +
          ∑ w, ∑ i, (packing.multiplicity w : ℤ) *
            (q i * e7Weight4 w.1.2 i) := by
      simp only [integerDot]
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ = q₀ * ∑ w, (packing.multiplicity w : ℤ) +
          ∑ i, q i *
            ∑ w, (packing.multiplicity w : ℤ) *
              e7Weight4 w.1.2 i := by
      rw [Finset.sum_comm]
      apply congrArg₂ (· + ·)
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
      · apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
    _ = q₀ * 220 + ∑ i, q i * (110 * d₂ i) := by
      have htotalZ :
          (∑ w, (packing.multiplicity w : ℤ)) = 220 := by
        exact_mod_cast packing.total
      rw [htotalZ]
      apply congrArg (q₀ * 220 + ·)
      apply Finset.sum_congr rfl
      intro i _
      rw [packing.rightCentroid i]
    _ = q₀ * 220 + 110 * integerDot q d₂ := by
      simp only [integerDot]
      rw [Finset.mul_sum]
      apply congrArg (q₀ * 220 + ·)
      apply Finset.sum_congr rfl
      intro i _
      ring

private theorem sum_le_six_of_card_le_two
    {V : Type*} [DecidableEq V]
    (m : V → ℕ) (s : Finset V)
    (hm : ∀ v, m v ≤ 3) (hcard : s.card ≤ 2) :
    ∑ v ∈ s, m v ≤ 6 := by
  calc
    (∑ v ∈ s, m v) ≤ s.card • 3 :=
      Finset.sum_le_card_nsmul s m 3 (fun v _ => hm v)
    _ = s.card * 3 := by simp
    _ ≤ 2 * 3 := Nat.mul_le_mul_right 3 hcard
    _ = 6 := by norm_num

/-- Generic capacity contradiction used by the `6g × 6g` residual shell.

Each component contains at most two vertices on either Boolean side, and
every cross-side pair in a component has negative inner product.  A packing
therefore uses at most one side and has total multiplicity at most six in
each component.  Thirty-six components have capacity only 216. -/
theorem no_e7ShellPacking_of_bipartite_components
    {d₁ d₂ : Fin 8 → ℤ}
    {K : Type*} [Fintype K] [DecidableEq K]
    (components : K → Finset (E7ResidualEligibleIndex d₁ d₂))
    (owner : E7ResidualEligibleIndex d₁ d₂ → K)
    (side : E7ResidualEligibleIndex d₁ d₂ → Bool)
    (hmem : ∀ k v, v ∈ components k ↔ owner v = k)
    (hside :
      ∀ k b, ((components k).filter fun v => side v = b).card ≤ 2)
    (hnegative :
      ∀ k u, u ∈ components k →
        ∀ v, v ∈ components k → side u ≠ side v →
          e7ShellInner u.1 v.1 < 0)
    (hcard : Fintype.card K ≤ 36) :
    IsEmpty (E7ShellPacking d₁ d₂) := by
  refine ⟨fun packing => ?_⟩
  let m := packing.multiplicity
  have hcomponent (k : K) :
      ∑ v ∈ components k, m v ≤ 6 := by
    let left := (components k).filter fun v => side v = false
    let right := (components k).filter fun v => side v = true
    have hsplit :
        (∑ v ∈ components k, m v) =
          (∑ v ∈ left, m v) + ∑ v ∈ right, m v := by
      rw [← Finset.sum_filter_add_sum_filter_not
        (components k) (fun v => side v = false) m]
      congr 2
      ext v
      simp [right]
    by_cases hleft : ∃ u ∈ left, 0 < m u
    · obtain ⟨u, hu, hmu⟩ := hleft
      have huraw : u ∈ components k := (Finset.mem_filter.mp hu).1
      have huside : side u = false := (Finset.mem_filter.mp hu).2
      have hrightzero : ∀ v ∈ right, m v = 0 := by
        intro v hv
        have hvraw : v ∈ components k := (Finset.mem_filter.mp hv).1
        have hvside : side v = true := (Finset.mem_filter.mp hv).2
        by_contra hmv
        have hmvpos : 0 < m v := Nat.pos_of_ne_zero hmv
        have hneg := hnegative k u huraw v hvraw (by simp [huside, hvside])
        have hnonneg := packing.nonnegative u v hmu hmvpos
        omega
      rw [hsplit, Finset.sum_eq_zero hrightzero, add_zero]
      exact sum_le_six_of_card_le_two m left packing.le_three
        (hside k false)
    · have hleftzero : ∀ u ∈ left, m u = 0 := by
        intro u hu
        exact Nat.eq_zero_of_not_pos (fun hmu => hleft ⟨u, hu, hmu⟩)
      rw [hsplit, Finset.sum_eq_zero hleftzero, zero_add]
      exact sum_le_six_of_card_le_two m right packing.le_three
        (hside k true)
  have hcomponents_eq (k : K) :
      components k = Finset.univ.filter fun v => owner v = k := by
    ext v
    simp [hmem]
  have htotal_by_components :
      ∑ k, ∑ v ∈ components k, m v = ∑ v, m v := by
    simp_rw [hcomponents_eq, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have hcapacity :
      (∑ k, ∑ v ∈ components k, m v) ≤
        Fintype.card K * 6 := by
    calc
      (∑ k, ∑ v ∈ components k, m v) ≤ ∑ _k : K, 6 :=
        Finset.sum_le_sum fun k _ => hcomponent k
      _ = Fintype.card K * 6 := by simp
  rw [htotal_by_components, packing.total] at hcapacity
  have : Fintype.card K * 6 ≤ 36 * 6 :=
    Nat.mul_le_mul_right 6 hcard
  omega

end SRG266
