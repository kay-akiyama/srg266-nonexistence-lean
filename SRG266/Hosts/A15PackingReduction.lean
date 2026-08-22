/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.ShellGram
import SRG266.Hosts.A15Plus
import SRG266.NotOneIntegrable
import SRG266.Hosts.A15Parity
import SRG266.Hosts.A15PackingParityTheory

/-!
# Direct A15 shell realizations and the binary residual profiles

This module gives the coordinate-level realization used at the `A₁₅⁺`
classification boundary.  Its vectors are the oriented four-subset vectors
already used by the centroid certificates.

For the two extreme projector survivors, all 220 occurrences lie in one
orbit.  At centroid profiles 0 and 12 that orbit is naturally indexed by the
three-subsets of a twelve-element coordinate class.  A finite exact theorem
checks the Gram law

`⟨v_S,v_T⟩ = |S ∩ T|`.

Consequently either survivor supplies an integral weight-three factorization
of the local Gram matrix.  No Python assertion about the endpoint is trusted.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Exact inner product of two oriented A15 shell vectors. -/
def a15ShellInner
    (d : Fin 16 → ℤ) (s t : A15EligibleIndex d) : ℤ :=
  integerDot (a15ShellVector4 d s) (a15ShellVector4 d t) / 16

/-- A direct coordinate realization of the 220 local Gram occurrences in an
oriented A15 four-subset shell. -/
structure A15ShellGramRealization
    (x : V) (d : Fin 16 → ℤ) where
  shell : SecondSubconstituent G x → A15EligibleIndex d
  gram :
    ∀ B C, a15ShellInner d (shell B) (shell C) =
      localGramMatrix G x B C
  eq_of_inner_eq_three :
    ∀ s t, a15ShellInner d s t = 3 → s = t
  centroid :
    ∀ i, ∑ B, a15ShellVector4 d (shell B) i = 11 * d i

def A15ShellGramRealization.toFiniteShell
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) :
    FiniteShellGramRealization G x (A15EligibleIndex d)
      (a15ShellInner d) where
  shell := realization.shell
  gram := realization.gram
  eq_of_inner_eq_three := realization.eq_of_inner_eq_three

/-- Profile 0 of the A15 centroid-survivor list. -/
def a15BinaryProfile0 : Fin 16 → ℤ :=
  ![-60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 20, 20]

/-- Profile 12, the sign-reversed companion of profile 0. -/
def a15BinaryProfile12 : Fin 16 → ℤ :=
  ![-20, -20, -20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60]

def a15BinaryCoordinate0 (j : Fin 12) : Fin 16 :=
  ⟨j.1 + 1, by omega⟩

def a15BinaryCoordinate12 (j : Fin 12) : Fin 16 :=
  ⟨j.1 + 3, by omega⟩

def a15BinaryEntry0
    (s : A15EligibleIndex a15BinaryProfile0)
    (j : Fin 12) : ℤ :=
  if a15BinaryCoordinate0 j ∈ a15FourSubsetAsFinset s.1 then 1 else 0

def a15BinaryEntry12
    (s : A15EligibleIndex a15BinaryProfile12)
    (j : Fin 12) : ℤ :=
  if a15BinaryCoordinate12 j ∈ a15FourSubsetAsFinset s.1 then 1 else 0

private def a15RawCoordinate4
    (s : Finset (Fin 16)) (i : Fin 16) : ℤ :=
  if i ∈ s then -3 else 1

private theorem a15FourSubsetAsFinset_card
    (s : A15FourSubsetIndex) :
    (a15FourSubsetAsFinset s).card = 4 := by
  unfold a15FourSubsetAsFinset A15FourSubset.asFinset
  rw [List.toFinset_card_of_nodup
    (a15FourSubsetAt_coordinates_nodup s)]
  rfl

private theorem a15_sum_indicator
    (s : Finset (Fin 16)) :
    (∑ i, if i ∈ s then (1 : ℤ) else 0) = s.card := by
  simp

private theorem a15_sum_double_indicator
    (s t : Finset (Fin 16)) :
    (∑ i, (if i ∈ s then (1 : ℤ) else 0) *
      (if i ∈ t then (1 : ℤ) else 0)) = (s ∩ t).card := by
  calc
    _ = ∑ i, if i ∈ s ∩ t then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
        simp [his, hit]
    _ = _ := a15_sum_indicator (s ∩ t)

/-- Cleared dot-product formula for two raw four-subset vectors. -/
private theorem a15_raw_dot
    (s t : Finset (Fin 16))
    (hs : s.card = 4) (ht : t.card = 4) :
    integerDot (a15RawCoordinate4 s) (a15RawCoordinate4 t) =
      16 * (((s ∩ t).card : ℤ) - 1) := by
  have hone : (∑ _i : Fin 16, (1 : ℤ)) = 16 := by norm_num
  have hs' := a15_sum_indicator s
  have ht' := a15_sum_indicator t
  have hst := a15_sum_double_indicator s t
  unfold integerDot a15RawCoordinate4
  have hexpand :
      (∑ i : Fin 16,
        (if i ∈ s then (-3 : ℤ) else 1) *
          (if i ∈ t then (-3 : ℤ) else 1)) =
        16 * (((s ∩ t).card : ℤ) - 1) := by
    calc
      _ = ∑ i : Fin 16,
          ((1 : ℤ) -
              4 * (if i ∈ s then (1 : ℤ) else 0)) *
            ((1 : ℤ) -
              4 * (if i ∈ t then (1 : ℤ) else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
          simp [his, hit]
      _ = (∑ _i : Fin 16, (1 : ℤ)) -
          4 * (∑ i, if i ∈ s then (1 : ℤ) else 0) -
          4 * (∑ i, if i ∈ t then (1 : ℤ) else 0) +
          16 * (∑ i,
            (if i ∈ s then (1 : ℤ) else 0) *
              (if i ∈ t then (1 : ℤ) else 0)) := by
        simp only [sub_mul, mul_sub,
          Finset.sum_sub_distrib, Finset.mul_sum]
        ring_nf
      _ = 16 * (((s ∩ t).card : ℤ) - 1) := by
        rw [hone, hs', ht', hst, hs, ht]
        ring
  exact hexpand

/-- The raw four-subset vectors have inner product one less than their
intersection size. -/
private theorem a15_raw_inner
    (s t : Finset (Fin 16))
    (hs : s.card = 4) (ht : t.card = 4) :
    integerDot (a15RawCoordinate4 s) (a15RawCoordinate4 t) / 16 =
      ((s ∩ t).card : ℤ) - 1 := by
  rw [a15_raw_dot s t hs ht]
  omega

/-- Clearing the denominator in the oriented A15 shell inner product
introduces exactly the factor 16. -/
theorem a15ShellVector4_dot_eq
    (d : Fin 16 → ℤ) (s t : A15EligibleIndex d) :
    integerDot (a15ShellVector4 d s) (a15ShellVector4 d t) =
      16 * a15ShellInner d s t := by
  let S := a15FourSubsetAsFinset s.1
  let T := a15FourSubsetAsFinset t.1
  have hS : S.card = 4 := a15FourSubsetAsFinset_card s.1
  have hT : T.card = 4 := a15FourSubsetAsFinset_card t.1
  have hraw := a15_raw_dot S T hS hT
  change
    integerDot (a15RawCoordinate4 S) (a15RawCoordinate4 T) =
      16 * (((S ∩ T).card : ℤ) - 1) at hraw
  let εs : ℤ := if a15SubsetSum d s.1 = 60 then -1 else 1
  let εt : ℤ := if a15SubsetSum d t.1 = 60 then -1 else 1
  have hscoord (i : Fin 16) :
      a15ShellVector4 d s i = εs * a15RawCoordinate4 S i := by
    by_cases hs : a15SubsetSum d s.1 = 60 <;>
      by_cases hi : i ∈ a15FourSubsetAsFinset s.1 <;>
        simp [a15ShellVector4, a15ShellCoordinate4,
          a15RawCoordinate4, S, εs, hs, hi]
  have htcoord (i : Fin 16) :
      a15ShellVector4 d t i = εt * a15RawCoordinate4 T i := by
    by_cases ht : a15SubsetSum d t.1 = 60 <;>
      by_cases hi : i ∈ a15FourSubsetAsFinset t.1 <;>
        simp [a15ShellVector4, a15ShellCoordinate4,
          a15RawCoordinate4, T, εt, ht, hi]
  have horiented :
      integerDot (a15ShellVector4 d s) (a15ShellVector4 d t) =
        (εs * εt) *
          integerDot (a15RawCoordinate4 S) (a15RawCoordinate4 T) := by
    unfold integerDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hscoord i, htcoord i]
    ring
  have hdiv :
      (16 : ℤ) ∣
        integerDot (a15ShellVector4 d s) (a15ShellVector4 d t) := by
    refine ⟨(εs * εt) * (((S ∩ T).card : ℤ) - 1), ?_⟩
    rw [horiented, hraw]
    ring
  unfold a15ShellInner
  rw [mul_comm]
  exact (Int.ediv_mul_cancel hdiv).symm

private def a15BinarySupport0
    (s : A15EligibleIndex a15BinaryProfile0) : Finset (Fin 12) :=
  Finset.univ.filter fun j => a15BinaryEntry0 s j = 1

private def a15BinarySupport12
    (s : A15EligibleIndex a15BinaryProfile12) : Finset (Fin 12) :=
  Finset.univ.filter fun j => a15BinaryEntry12 s j = 1

private theorem a15BinaryProfile0_apply (i : Fin 16) :
    a15BinaryProfile0 i =
      (if i = 0 then -60 else 0) +
        (if i = 13 then 20 else 0) +
        (if i = 14 then 20 else 0) +
        (if i = 15 then 20 else 0) := by
  fin_cases i <;> rfl

private theorem a15BinaryProfile12_apply (i : Fin 16) :
    a15BinaryProfile12 i =
      (if i = 0 then -20 else 0) +
        (if i = 1 then -20 else 0) +
        (if i = 2 then -20 else 0) +
        (if i = 15 then 60 else 0) := by
  fin_cases i <;> rfl

private theorem a15BinaryProfile0_sum_formula
    (s : A15EligibleIndex a15BinaryProfile0)
    (hs : a15SubsetContains s 0) :
    a15SubsetSum a15BinaryProfile0 s.1 =
      -60 + 20 *
        ((if (13 : Fin 16) ∈ a15FourSubsetAsFinset s.1 then 1 else 0) +
          (if (14 : Fin 16) ∈ a15FourSubsetAsFinset s.1 then 1 else 0) +
          (if (15 : Fin 16) ∈ a15FourSubsetAsFinset s.1 then 1 else 0)) := by
  classical
  have hs' : (0 : Fin 16) ∈ a15FourSubsetAsFinset s.1 := hs
  unfold a15SubsetSum a15DataSubsetSum
  rw [a15FourSubset_valueSum_eq_finset_sum]
  simp_rw [a15BinaryProfile0_apply]
  simp only [Finset.sum_add_distrib]
  by_cases h13 : (13 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    by_cases h14 : (14 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    by_cases h15 : (15 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    simp [hs', h13, h14, h15]

private theorem a15BinaryProfile12_sum_formula
    (s : A15EligibleIndex a15BinaryProfile12)
    (hs : a15SubsetContains s 15) :
    a15SubsetSum a15BinaryProfile12 s.1 =
      60 - 20 *
        ((if (0 : Fin 16) ∈ a15FourSubsetAsFinset s.1 then 1 else 0) +
          (if (1 : Fin 16) ∈ a15FourSubsetAsFinset s.1 then 1 else 0) +
          (if (2 : Fin 16) ∈ a15FourSubsetAsFinset s.1 then 1 else 0)) := by
  classical
  have hs' : (15 : Fin 16) ∈ a15FourSubsetAsFinset s.1 := hs
  unfold a15SubsetSum a15DataSubsetSum
  rw [a15FourSubset_valueSum_eq_finset_sum]
  simp_rw [a15BinaryProfile12_apply]
  simp only [Finset.sum_add_distrib]
  by_cases h0 : (0 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    by_cases h1 : (1 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    by_cases h2 : (2 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    simp [hs', h0, h1, h2]

private theorem a15BinaryProfile0_subsetSum
    (s : A15EligibleIndex a15BinaryProfile0)
    (hs : a15SubsetContains s 0) :
    a15SubsetSum a15BinaryProfile0 s.1 = -60 := by
  have heligible :
      a15SubsetSum a15BinaryProfile0 s.1 = -60 ∨
        a15SubsetSum a15BinaryProfile0 s.1 = 60 := s.2
  have hsum := a15BinaryProfile0_sum_formula s hs
  rw [hsum] at heligible ⊢
  by_cases h13 : (13 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    by_cases h14 : (14 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    by_cases h15 : (15 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    simp [h13, h14, h15] at heligible ⊢

private theorem a15BinaryProfile12_subsetSum
    (s : A15EligibleIndex a15BinaryProfile12)
    (hs : a15SubsetContains s 15) :
    a15SubsetSum a15BinaryProfile12 s.1 = 60 := by
  have heligible :
      a15SubsetSum a15BinaryProfile12 s.1 = -60 ∨
        a15SubsetSum a15BinaryProfile12 s.1 = 60 := s.2
  have hsum := a15BinaryProfile12_sum_formula s hs
  rw [hsum] at heligible ⊢
  by_cases h0 : (0 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    by_cases h1 : (1 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    by_cases h2 : (2 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
    simp [h0, h1, h2] at heligible ⊢

private theorem a15_mem_binarySupport0_image
    (s : A15EligibleIndex a15BinaryProfile0) (i : Fin 16) :
    i ∈ (a15BinarySupport0 s).image a15BinaryCoordinate0 ↔
      i ∈ a15FourSubsetAsFinset s.1 ∧ 1 ≤ i.1 ∧ i.1 ≤ 12 := by
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hj' :
        a15BinaryCoordinate0 j ∈ a15FourSubsetAsFinset s.1 := by
      simpa [a15BinarySupport0, a15BinaryEntry0] using hj
    exact ⟨hj', by simp [a15BinaryCoordinate0], by
      simp [a15BinaryCoordinate0]⟩
  · rintro ⟨hi, hi1, hi12⟩
    let j : Fin 12 := ⟨i.1 - 1, by omega⟩
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, ?_⟩
    · simp only [a15BinarySupport0, Finset.mem_filter, Finset.mem_univ,
        true_and, a15BinaryEntry0]
      have heq : a15BinaryCoordinate0 j = i := by
        apply Fin.ext
        simp [a15BinaryCoordinate0, j]
        omega
      simp [heq, hi]
    · apply Fin.ext
      simp [a15BinaryCoordinate0, j]
      omega

private theorem a15_mem_binarySupport12_image
    (s : A15EligibleIndex a15BinaryProfile12) (i : Fin 16) :
    i ∈ (a15BinarySupport12 s).image a15BinaryCoordinate12 ↔
      i ∈ a15FourSubsetAsFinset s.1 ∧ 3 ≤ i.1 ∧ i.1 ≤ 14 := by
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hj' :
        a15BinaryCoordinate12 j ∈ a15FourSubsetAsFinset s.1 := by
      simpa [a15BinarySupport12, a15BinaryEntry12] using hj
    exact ⟨hj', by simp [a15BinaryCoordinate12], by
      simp [a15BinaryCoordinate12]
      omega⟩
  · rintro ⟨hi, hi3, hi14⟩
    let j : Fin 12 := ⟨i.1 - 3, by omega⟩
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, ?_⟩
    · simp only [a15BinarySupport12, Finset.mem_filter, Finset.mem_univ,
        true_and, a15BinaryEntry12]
      have heq : a15BinaryCoordinate12 j = i := by
        apply Fin.ext
        simp [a15BinaryCoordinate12, j]
        omega
      simp [heq, hi]
    · apply Fin.ext
      simp [a15BinaryCoordinate12, j]
      omega

private theorem a15BinaryProfile0_subset
    (s : A15EligibleIndex a15BinaryProfile0)
    (hs : a15SubsetContains s 0) :
    a15FourSubsetAsFinset s.1 =
      insert 0 ((a15BinarySupport0 s).image a15BinaryCoordinate0) := by
  classical
  have hformula := a15BinaryProfile0_sum_formula s hs
  rw [a15BinaryProfile0_subsetSum s hs] at hformula
  have h13 : (13 : Fin 16) ∉ a15FourSubsetAsFinset s.1 := by
    intro h
    by_cases h14 : (14 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
      by_cases h15 : (15 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
      simp [h, h14, h15] at hformula
  have h14 : (14 : Fin 16) ∉ a15FourSubsetAsFinset s.1 := by
    intro h
    by_cases h15 : (15 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
      simp [h13, h, h15] at hformula
  have h15 : (15 : Fin 16) ∉ a15FourSubsetAsFinset s.1 := by
    intro h
    simp [h13, h14, h] at hformula
  ext i
  rw [Finset.mem_insert, a15_mem_binarySupport0_image]
  constructor
  · intro hi
    by_cases hi0 : i = 0
    · exact Or.inl hi0
    · right
      refine ⟨hi, ?_, ?_⟩
      · have hi0val : i.1 ≠ 0 := by
          intro h
          apply hi0
          apply Fin.ext
          simpa using h
        omega
      · have hi13val : i.1 ≠ 13 := by
          intro h
          apply h13
          have : i = 13 := by apply Fin.ext; simpa using h
          simpa [this] using hi
        have hi14val : i.1 ≠ 14 := by
          intro h
          apply h14
          have : i = 14 := by apply Fin.ext; simpa using h
          simpa [this] using hi
        have hi15val : i.1 ≠ 15 := by
          intro h
          apply h15
          have : i = 15 := by apply Fin.ext; simpa using h
          simpa [this] using hi
        omega
  · rintro (hi | ⟨hi, _, _⟩)
    · subst i
      exact hs
    · exact hi

private theorem a15BinaryProfile12_subset
    (s : A15EligibleIndex a15BinaryProfile12)
    (hs : a15SubsetContains s 15) :
    a15FourSubsetAsFinset s.1 =
      insert 15 ((a15BinarySupport12 s).image a15BinaryCoordinate12) := by
  classical
  have hformula := a15BinaryProfile12_sum_formula s hs
  rw [a15BinaryProfile12_subsetSum s hs] at hformula
  have h0 : (0 : Fin 16) ∉ a15FourSubsetAsFinset s.1 := by
    intro h
    by_cases h1 : (1 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
      by_cases h2 : (2 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
      simp [h, h1, h2] at hformula
  have h1 : (1 : Fin 16) ∉ a15FourSubsetAsFinset s.1 := by
    intro h
    by_cases h2 : (2 : Fin 16) ∈ a15FourSubsetAsFinset s.1 <;>
      simp [h0, h, h2] at hformula
  have h2 : (2 : Fin 16) ∉ a15FourSubsetAsFinset s.1 := by
    intro h
    simp [h0, h1, h] at hformula
  ext i
  rw [Finset.mem_insert, a15_mem_binarySupport12_image]
  constructor
  · intro hi
    by_cases hi15 : i = 15
    · exact Or.inl hi15
    · right
      refine ⟨hi, ?_, ?_⟩
      · have hi0val : i.1 ≠ 0 := by
          intro h
          apply h0
          have : i = 0 := by apply Fin.ext; simpa using h
          simpa [this] using hi
        have hi1val : i.1 ≠ 1 := by
          intro h
          apply h1
          have : i = 1 := by apply Fin.ext; simpa using h
          simpa [this] using hi
        have hi2val : i.1 ≠ 2 := by
          intro h
          apply h2
          have : i = 2 := by apply Fin.ext; simpa using h
          simpa [this] using hi
        omega
      · have hi15val : i.1 ≠ 15 := by
          intro h
          apply hi15
          apply Fin.ext
          simpa using h
        omega
  · rintro (hi | ⟨hi, _, _⟩)
    · subst i
      exact hs
    · exact hi

private theorem a15BinaryCoordinate0_injective :
    Function.Injective a15BinaryCoordinate0 := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [a15BinaryCoordinate0] at hval
  omega

private theorem a15BinaryCoordinate12_injective :
    Function.Injective a15BinaryCoordinate12 := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [a15BinaryCoordinate12] at hval
  omega

private theorem a15_binary_sum_indicator
    (u : Finset (Fin 12)) :
    (∑ j, if j ∈ u then (1 : ℤ) else 0) = u.card := by
  simp

private theorem a15_binary_sum_eq_inter_card
    (u v : Finset (Fin 12)) :
    (∑ j, (if j ∈ u then (1 : ℤ) else 0) *
      (if j ∈ v then (1 : ℤ) else 0)) = (u ∩ v).card := by
  calc
    _ = ∑ j, if j ∈ u ∩ v then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hju : j ∈ u <;> by_cases hjv : j ∈ v <;>
        simp [hju, hjv]
    _ = _ := a15_binary_sum_indicator (u ∩ v)

private theorem a15_insert_image_inter_card
    (anchor : Fin 16) (f : Fin 12 → Fin 16)
    (hf : Function.Injective f)
    (hanchor : ∀ j, f j ≠ anchor)
    (u v : Finset (Fin 12)) :
    ((insert anchor (u.image f)) ∩
      (insert anchor (v.image f))).card =
      1 + (u ∩ v).card := by
  have hinter :
      (insert anchor (u.image f)) ∩
          (insert anchor (v.image f)) =
        insert anchor ((u ∩ v).image f) := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨hi | ⟨j, hju, rfl⟩, hi'⟩
      · exact Or.inl hi
      · right
        rcases hi' with hi' | ⟨k, hkv, hk⟩
        · exact (hanchor j hi').elim
        · have hjk : j = k := hf hk.symm
          subst k
          exact ⟨j, by simp [hju, hkv]⟩
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨Or.inl rfl, Or.inl rfl⟩
      · have hparts : j ∈ u ∧ j ∈ v := hj
        exact
          ⟨Or.inr ⟨j, hparts.1, rfl⟩,
            Or.inr ⟨j, hparts.2, rfl⟩⟩
  rw [hinter, Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective _ hf]
    omega
  · simp only [Finset.mem_image, not_exists]
    intro j hj
    exact hanchor j hj.2

private theorem a15_insert_image_inter_card8
    (anchor : Fin 16) (f : Fin 8 → Fin 16)
    (hf : Function.Injective f)
    (hanchor : ∀ j, f j ≠ anchor)
    (u v : Finset (Fin 8)) :
    ((insert anchor (u.image f)) ∩
      (insert anchor (v.image f))).card =
      1 + (u ∩ v).card := by
  have hinter :
      (insert anchor (u.image f)) ∩
          (insert anchor (v.image f)) =
        insert anchor ((u ∩ v).image f) := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨hi | ⟨j, hju, rfl⟩, hi'⟩
      · exact Or.inl hi
      · right
        rcases hi' with hi' | ⟨k, hkv, hk⟩
        · exact (hanchor j hi').elim
        · have hjk : j = k := hf hk.symm
          subst k
          exact ⟨j, by simp [hju, hkv]⟩
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨Or.inl rfl, Or.inl rfl⟩
      · have hparts : j ∈ u ∧ j ∈ v := hj
        exact
          ⟨Or.inr ⟨j, hparts.1, rfl⟩,
            Or.inr ⟨j, hparts.2, rfl⟩⟩
  rw [hinter, Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective _ hf]
    omega
  · simp only [Finset.mem_image, not_exists]
    intro j hj
    exact hanchor j hj.2

/-- Exact Johnson-triple Gram law for the selected profile-0 orbit. -/
theorem a15BinaryProfile0_gram
    (s t : A15EligibleIndex a15BinaryProfile0)
    (hs : a15SubsetContains s 0)
    (ht : a15SubsetContains t 0) :
    (∑ j, a15BinaryEntry0 s j * a15BinaryEntry0 t j) =
      a15ShellInner a15BinaryProfile0 s t := by
  let S := a15FourSubsetAsFinset s.1
  let T := a15FourSubsetAsFinset t.1
  have hsumS := a15BinaryProfile0_subsetSum s hs
  have hsumT := a15BinaryProfile0_subsetSum t ht
  have hraw :
      a15ShellInner a15BinaryProfile0 s t =
        ((S ∩ T).card : ℤ) - 1 := by
    unfold a15ShellInner a15ShellVector4 a15ShellCoordinate4
    simp only [hsumS, hsumT]
    exact a15_raw_inner S T
      (a15FourSubsetAsFinset_card s.1)
      (a15FourSubsetAsFinset_card t.1)
  have hcard :
      (S ∩ T).card =
        1 + (a15BinarySupport0 s ∩ a15BinarySupport0 t).card := by
    change
      ((a15FourSubsetAsFinset s.1) ∩
        (a15FourSubsetAsFinset t.1)).card =
        1 + (a15BinarySupport0 s ∩
          a15BinarySupport0 t).card
    rw [a15BinaryProfile0_subset s hs,
      a15BinaryProfile0_subset t ht]
    exact a15_insert_image_inter_card 0 a15BinaryCoordinate0
      a15BinaryCoordinate0_injective
      (by intro j; simp [a15BinaryCoordinate0]) _ _
  rw [hraw, hcard]
  have hsum :=
    a15_binary_sum_eq_inter_card
      (a15BinarySupport0 s) (a15BinarySupport0 t)
  simpa [a15BinarySupport0, a15BinaryEntry0] using hsum

/-- Exact Johnson-triple Gram law for the selected profile-12 orbit. -/
theorem a15BinaryProfile12_gram
    (s t : A15EligibleIndex a15BinaryProfile12)
    (hs : a15SubsetContains s 15)
    (ht : a15SubsetContains t 15) :
    (∑ j, a15BinaryEntry12 s j * a15BinaryEntry12 t j) =
      a15ShellInner a15BinaryProfile12 s t := by
  let S := a15FourSubsetAsFinset s.1
  let T := a15FourSubsetAsFinset t.1
  have hsumS := a15BinaryProfile12_subsetSum s hs
  have hsumT := a15BinaryProfile12_subsetSum t ht
  have hraw :
      a15ShellInner a15BinaryProfile12 s t =
        ((S ∩ T).card : ℤ) - 1 := by
    unfold a15ShellInner a15ShellVector4 a15ShellCoordinate4
    simp only [hsumS, hsumT, ↓reduceIte]
    change
      integerDot (fun i => -a15RawCoordinate4 S i)
          (fun i => -a15RawCoordinate4 T i) / 16 =
        ((S ∩ T).card : ℤ) - 1
    have hneg :
        integerDot (fun i => -a15RawCoordinate4 S i)
            (fun i => -a15RawCoordinate4 T i) =
          integerDot (a15RawCoordinate4 S) (a15RawCoordinate4 T) := by
      unfold integerDot
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg]
    exact a15_raw_inner S T
      (a15FourSubsetAsFinset_card s.1)
      (a15FourSubsetAsFinset_card t.1)
  have hcard :
      (S ∩ T).card =
        1 + (a15BinarySupport12 s ∩
          a15BinarySupport12 t).card := by
    change
      ((a15FourSubsetAsFinset s.1) ∩
        (a15FourSubsetAsFinset t.1)).card =
        1 + (a15BinarySupport12 s ∩
          a15BinarySupport12 t).card
    rw [a15BinaryProfile12_subset s hs,
      a15BinaryProfile12_subset t ht]
    exact a15_insert_image_inter_card 15 a15BinaryCoordinate12
      a15BinaryCoordinate12_injective
      (by
        intro j hj
        have hval := congrArg Fin.val hj
        simp only [a15BinaryCoordinate12] at hval
        omega) _ _
  rw [hraw, hcard]
  have hsum :=
    a15_binary_sum_eq_inter_card
      (a15BinarySupport12 s) (a15BinarySupport12 t)
  simpa [a15BinarySupport12, a15BinaryEntry12] using hsum

/-- A profile-0 realization supported on its 220-element orbit is
one-integrable. -/
theorem A15ShellGramRealization.profile0_oneIntegrable
    {x : V}
    (realization :
      A15ShellGramRealization G x a15BinaryProfile0)
    (hselected :
      ∀ B, a15SubsetContains (realization.shell B) 0) :
    LocalGramIsOneIntegrable G x := by
  let W : Matrix (Fin 12) (SecondSubconstituent G x) ℤ :=
    fun j B => a15BinaryEntry0 (realization.shell B) j
  refine ⟨12, W, ?_⟩
  ext B C
  change
    (∑ j, a15BinaryEntry0 (realization.shell B) j *
      a15BinaryEntry0 (realization.shell C) j) =
      localGramMatrix G x B C
  rw [a15BinaryProfile0_gram
    (realization.shell B) (realization.shell C)
    (hselected B) (hselected C)]
  exact realization.gram B C

/-- A profile-12 realization supported on its 220-element orbit is
one-integrable. -/
theorem A15ShellGramRealization.profile12_oneIntegrable
    {x : V}
    (realization :
      A15ShellGramRealization G x a15BinaryProfile12)
    (hselected :
      ∀ B, a15SubsetContains (realization.shell B) 15) :
    LocalGramIsOneIntegrable G x := by
  let W : Matrix (Fin 12) (SecondSubconstituent G x) ℤ :=
    fun j B => a15BinaryEntry12 (realization.shell B) j
  refine ⟨12, W, ?_⟩
  ext B C
  change
    (∑ j, a15BinaryEntry12 (realization.shell B) j *
      a15BinaryEntry12 (realization.shell C) j) =
      localGramMatrix G x B C
  rw [a15BinaryProfile12_gram
    (realization.shell B) (realization.shell C)
    (hselected B) (hselected C)]
  exact realization.gram B C

private theorem a15ParityProfile1_inner_eq_inter_card
    (s t : A15ParityBIndex1) :
    a15ShellInner a15ParityProfile1 s.1 t.1 =
      ((a15ParitySupport1 s.1 ∩ a15ParitySupport1 t.1).card : ℤ) := by
  let S := a15FourSubsetAsFinset s.1.1
  let T := a15FourSubsetAsFinset t.1.1
  have hsumS := a15ParityShapeFacts.2.2.1 s.1 s.2
  have hsumT := a15ParityShapeFacts.2.2.1 t.1 t.2
  have hraw :
      a15ShellInner a15ParityProfile1 s.1 t.1 =
        ((S ∩ T).card : ℤ) - 1 := by
    unfold a15ShellInner a15ShellVector4 a15ShellCoordinate4
    simp only [hsumS, hsumT, ↓reduceIte]
    change
      integerDot (fun i => -a15RawCoordinate4 S i)
          (fun i => -a15RawCoordinate4 T i) / 16 =
        ((S ∩ T).card : ℤ) - 1
    have hneg :
        integerDot (fun i => -a15RawCoordinate4 S i)
            (fun i => -a15RawCoordinate4 T i) =
          integerDot (a15RawCoordinate4 S) (a15RawCoordinate4 T) := by
      unfold integerDot
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg]
    exact a15_raw_inner S T
      (a15FourSubsetAsFinset_card s.1.1)
      (a15FourSubsetAsFinset_card t.1.1)
  have hcard :
      (S ∩ T).card =
        1 + (a15ParitySupport1 s.1 ∩
          a15ParitySupport1 t.1).card := by
    change
      ((a15FourSubsetAsFinset s.1.1) ∩
        (a15FourSubsetAsFinset t.1.1)).card =
        1 + (a15ParitySupport1 s.1 ∩
          a15ParitySupport1 t.1).card
    rw [a15ParityShapeFacts.1 s.1 s.2,
      a15ParityShapeFacts.1 t.1 t.2]
    exact a15_insert_image_inter_card8 15 a15ParityCoordinate1
      a15ParityCoordinate1_injective
      (by
        intro j hj
        have hval := congrArg Fin.val hj
        simp only [a15ParityCoordinate1] at hval
        omega) _ _
  rw [hraw, hcard]
  omega

private theorem a15ParityProfile8_inner_eq_inter_card
    (s t : A15ParityBIndex8) :
    a15ShellInner a15ParityProfile8 s.1 t.1 =
      ((a15ParitySupport8 s.1 ∩ a15ParitySupport8 t.1).card : ℤ) := by
  let S := a15FourSubsetAsFinset s.1.1
  let T := a15FourSubsetAsFinset t.1.1
  have hsumS := a15ParityShapeFacts.2.2.2.1 s.1 s.2
  have hsumT := a15ParityShapeFacts.2.2.2.1 t.1 t.2
  have hraw :
      a15ShellInner a15ParityProfile8 s.1 t.1 =
        ((S ∩ T).card : ℤ) - 1 := by
    unfold a15ShellInner a15ShellVector4 a15ShellCoordinate4
    simp only [hsumS, hsumT]
    exact a15_raw_inner S T
      (a15FourSubsetAsFinset_card s.1.1)
      (a15FourSubsetAsFinset_card t.1.1)
  have hcard :
      (S ∩ T).card =
        1 + (a15ParitySupport8 s.1 ∩
          a15ParitySupport8 t.1).card := by
    change
      ((a15FourSubsetAsFinset s.1.1) ∩
        (a15FourSubsetAsFinset t.1.1)).card =
        1 + (a15ParitySupport8 s.1 ∩
          a15ParitySupport8 t.1).card
    rw [a15ParityShapeFacts.2.1 s.1 s.2,
      a15ParityShapeFacts.2.1 t.1 t.2]
    exact a15_insert_image_inter_card8 0 a15ParityCoordinate8
      a15ParityCoordinate8_injective
      (by intro j; simp [a15ParityCoordinate8]) _ _
  rw [hraw, hcard]
  omega

/-- The triple pair kernel agrees with the shell inner-product-two relation
on the profile-1 56-orbit. -/
theorem a15ParityProfile1_kernel
    (s t : A15ParityBIndex1) :
    a15ParityPairKernel (a15ParityTriple1 s) (a15ParityTriple1 t) =
      if s = t then 3
      else if a15ShellInner a15ParityProfile1 s.1 t.1 = 2 then 1 else 0 := by
  by_cases hst : s = t
  · simp [hst, a15ParityPairKernel]
  · have htriple : a15ParityTriple1 s ≠ a15ParityTriple1 t := by
      intro h
      exact hst (a15ParityShellEquiv1.symm.injective h)
    rw [a15ParityProfile1_inner_eq_inter_card]
    simp only [a15ParityPairKernel, hst, htriple, ↓reduceIte]
    norm_cast

/-- The same kernel compatibility for profile 8. -/
theorem a15ParityProfile8_kernel
    (s t : A15ParityBIndex8) :
    a15ParityPairKernel (a15ParityTriple8 s) (a15ParityTriple8 t) =
      if s = t then 3
      else if a15ShellInner a15ParityProfile8 s.1 t.1 = 2 then 1 else 0 := by
  by_cases hst : s = t
  · simp [hst, a15ParityPairKernel]
  · have htriple : a15ParityTriple8 s ≠ a15ParityTriple8 t := by
      intro h
      exact hst (a15ParityShellEquiv8.symm.injective h)
    rw [a15ParityProfile8_inner_eq_inter_card]
    simp only [a15ParityPairKernel, hst, htriple, ↓reduceIte]
    norm_cast

/-- No vector outside the 56-orbit has inner product two with a vector in
that orbit at profile 1. -/
theorem a15ParityProfile1_no_cross_two
    (s : A15ParityBIndex1)
    (t : A15EligibleIndex a15ParityProfile1)
    (ht : ¬a15SubsetContains t 15) :
    a15ShellInner a15ParityProfile1 s.1 t ≠ 2 := by
  let S := a15FourSubsetAsFinset s.1.1
  let T := a15FourSubsetAsFinset t.1
  let Y := Finset.univ.image a15ParityCoordinate1
  have hsumS := a15ParityShapeFacts.2.2.1 s.1 s.2
  have htFacts := a15ParityShapeFacts.2.2.2.2.1 t ht
  have hinner :
      a15ShellInner a15ParityProfile1 s.1 t =
        1 - ((S ∩ T).card : ℤ) := by
    unfold a15ShellInner a15ShellVector4 a15ShellCoordinate4
    simp only [hsumS, htFacts.1, ↓reduceIte]
    change
      integerDot (fun i => -a15RawCoordinate4 S i)
          (a15RawCoordinate4 T) / 16 =
        1 - ((S ∩ T).card : ℤ)
    have hneg :
        integerDot (fun i => -a15RawCoordinate4 S i)
            (a15RawCoordinate4 T) =
          -integerDot (a15RawCoordinate4 S)
            (a15RawCoordinate4 T) := by
      unfold integerDot
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg]
    rw [a15_raw_dot S T
      (a15FourSubsetAsFinset_card s.1.1)
      (a15FourSubsetAsFinset_card t.1)]
    omega
  have hsubset : S ∩ T ⊆ T ∩ Y := by
    intro i hi
    have hiS := (Finset.mem_inter.mp hi).1
    have hiT := (Finset.mem_inter.mp hi).2
    have hshape := a15ParityShapeFacts.1 s.1 s.2
    change i ∈ a15FourSubsetAsFinset s.1.1 at hiS
    rw [hshape] at hiS
    rcases Finset.mem_insert.mp hiS with hiAnchor | hiImage
    · subst i
      exact (ht hiT).elim
    · refine Finset.mem_inter.mpr ⟨hiT, ?_⟩
      rcases Finset.mem_image.mp hiImage with ⟨j, _, rfl⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hle : (S ∩ T).card ≤ 1 := by
    calc
      (S ∩ T).card ≤ (T ∩ Y).card :=
        Finset.card_le_card hsubset
      _ = 1 := htFacts.2
  omega

/-- No vector outside the 56-orbit has inner product two with a vector in
that orbit at profile 8. -/
theorem a15ParityProfile8_no_cross_two
    (s : A15ParityBIndex8)
    (t : A15EligibleIndex a15ParityProfile8)
    (ht : ¬a15SubsetContains t 0) :
    a15ShellInner a15ParityProfile8 s.1 t ≠ 2 := by
  let S := a15FourSubsetAsFinset s.1.1
  let T := a15FourSubsetAsFinset t.1
  let Y := Finset.univ.image a15ParityCoordinate8
  have hsumS := a15ParityShapeFacts.2.2.2.1 s.1 s.2
  have htFacts := a15ParityShapeFacts.2.2.2.2.2 t ht
  have hinner :
      a15ShellInner a15ParityProfile8 s.1 t =
        1 - ((S ∩ T).card : ℤ) := by
    unfold a15ShellInner a15ShellVector4 a15ShellCoordinate4
    simp only [hsumS, htFacts.1, ↓reduceIte]
    change
      integerDot (a15RawCoordinate4 S)
          (fun i => -a15RawCoordinate4 T i) / 16 =
        1 - ((S ∩ T).card : ℤ)
    have hneg :
        integerDot (a15RawCoordinate4 S)
            (fun i => -a15RawCoordinate4 T i) =
          -integerDot (a15RawCoordinate4 S)
            (a15RawCoordinate4 T) := by
      unfold integerDot
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg]
    rw [a15_raw_dot S T
      (a15FourSubsetAsFinset_card s.1.1)
      (a15FourSubsetAsFinset_card t.1)]
    omega
  have hsubset : S ∩ T ⊆ T ∩ Y := by
    intro i hi
    have hiS := (Finset.mem_inter.mp hi).1
    have hiT := (Finset.mem_inter.mp hi).2
    have hshape := a15ParityShapeFacts.2.1 s.1 s.2
    change i ∈ a15FourSubsetAsFinset s.1.1 at hiS
    rw [hshape] at hiS
    rcases Finset.mem_insert.mp hiS with hiAnchor | hiImage
    · subst i
      exact (ht hiT).elim
    · refine Finset.mem_inter.mpr ⟨hiT, ?_⟩
      rcases Finset.mem_image.mp hiImage with ⟨j, _, rfl⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hle : (S ∩ T).card ≤ 1 := by
    calc
      (S ∩ T).card ≤ (T ∩ Y).card :=
        Finset.card_le_card hsubset
      _ = 1 := htFacts.2
  omega

end SRG266
