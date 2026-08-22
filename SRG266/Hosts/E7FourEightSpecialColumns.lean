/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7FourEightSpecialShell

/-!
# Column identities for the special `4 × 8` E7 residual

Integral affine functionals pair the twelve second-factor columns and show
that the six positive representatives have total multiplicity 110.
-/

open scoped BigOperators

namespace SRG266
namespace E7FourEightSpecial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def positiveColumns : List SecondWeight :=
  [⟨(false, ⟨12, by decide⟩), by decide⟩,
   ⟨(false, ⟨17, by decide⟩), by decide⟩,
   ⟨(false, ⟨21, by decide⟩), by decide⟩,
   ⟨(false, ⟨24, by decide⟩), by decide⟩,
   ⟨(false, ⟨26, by decide⟩), by decide⟩,
   ⟨(false, ⟨27, by decide⟩), by decide⟩]

def negativeColumns : List SecondWeight :=
  [⟨(true, ⟨0, by decide⟩), by decide⟩,
   ⟨(true, ⟨1, by decide⟩), by decide⟩,
   ⟨(true, ⟨2, by decide⟩), by decide⟩,
   ⟨(true, ⟨3, by decide⟩), by decide⟩,
   ⟨(true, ⟨4, by decide⟩), by decide⟩,
   ⟨(true, ⟨5, by decide⟩), by decide⟩]

abbrev PairIndex := Fin positiveColumns.length

def positiveColumn (r : PairIndex) : SecondWeight :=
  positiveColumns.get r

def negativeColumn (r : PairIndex) : SecondWeight :=
  negativeColumns.get
    ⟨r.1, by
      have hr := r.2
      simp [positiveColumns, negativeColumns] at hr ⊢⟩

def pairCoordinate (r : PairIndex) : Fin 8 :=
  ⟨r.1 + 1, by
    have := r.2
    simp only [positiveColumns, List.length_cons, List.length_nil] at this
    omega⟩

def pairFunctional (r : PairIndex) : Fin 8 → ℤ :=
  fun i => if i = 0 ∨ i = pairCoordinate r then 1 else 0

theorem pairFunctional_value (r : PairIndex) (b : SecondWeight) :
    2 + integerDot (pairFunctional r) (e7Weight4 b.1) =
      4 * ((if b = positiveColumn r then 1 else 0) -
        if b = negativeColumn r then 1 else 0) := by
  decide +kernel +revert

private theorem sum_mul_indicator
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℤ) (a : α) :
    ∑ x, f x * (if x = a then 1 else 0) = f a := by
  classical
  simp

private theorem sum_get
    {α M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → M) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  rw [List.ofFn_comp']
  exact congrArg (List.map f) (List.ofFn_get l)

private theorem sum_mul_indicator_list
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℤ) (l : List α) (hl : l.Nodup) :
    ∑ x, f x * (if x ∈ l then 1 else 0) =
      ∑ i : Fin l.length, f (l.get i) := by
  rw [sum_get]
  rw [← List.sum_toFinset f hl]
  calc
    _ = ∑ x, if x ∈ l then f x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split <;> simp_all
    _ = ∑ x ∈ Finset.univ.filter (fun x => x ∈ l), f x := by
      rw [Finset.sum_filter]
    _ = l.toFinset.sum f := by
      congr 1
      ext x
      simp

theorem pairFunctional_rhs (r : PairIndex) :
    (2 : ℤ) * 220 + 110 * integerDot (pairFunctional r) d₈ = 0 := by
  fin_cases r <;> rfl

theorem paired_column_totals_equal
    (packing : E7ShellPacking d₄ d₈) (r : PairIndex) :
    columnTotal packing (positiveColumn r) =
      columnTotal packing (negativeColumn r) := by
  have h := right_affine_by_columns packing 2 (pairFunctional r)
  simp_rw [pairFunctional_value r] at h
  rw [pairFunctional_rhs r] at h
  have hleft :
      ∑ b : SecondWeight, (columnTotal packing b : ℤ) *
          (4 * ((if b = positiveColumn r then 1 else 0) -
            if b = negativeColumn r then 1 else 0)) =
        4 * ((columnTotal packing (positiveColumn r) : ℤ) -
          columnTotal packing (negativeColumn r)) := by
    calc
      _ = ∑ b : SecondWeight,
          (4 * ((columnTotal packing b : ℤ) *
            (if b = positiveColumn r then 1 else 0)) -
          4 * ((columnTotal packing b : ℤ) *
            (if b = negativeColumn r then 1 else 0))) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = 4 * (
          (∑ b : SecondWeight, (columnTotal packing b : ℤ) *
            (if b = positiveColumn r then 1 else 0)) -
          ∑ b : SecondWeight, (columnTotal packing b : ℤ) *
            (if b = negativeColumn r then 1 else 0)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
      _ = _ := by
        rw [sum_mul_indicator, sum_mul_indicator]
  rw [hleft] at h
  omega

def representativeFunctional : Fin 8 → ℤ :=
  fun i => if i = 0 then 1 else 0

theorem representativeFunctional_value (b : SecondWeight) :
    3 + integerDot representativeFunctional (e7Weight4 b.1) =
      2 * if b ∈ positiveColumns then 1 else 0 := by
  decide +kernel +revert

theorem positiveColumns_nodup : positiveColumns.Nodup := by
  decide +kernel

theorem representative_column_total
    (packing : E7ShellPacking d₄ d₈) :
    ∑ r : PairIndex, columnTotal packing (positiveColumn r) = 110 := by
  have h := right_affine_by_columns packing 3 representativeFunctional
  have hrhs :
      (3 : ℤ) * 220 + 110 * integerDot representativeFunctional d₈ =
        220 := by
    rfl
  rw [hrhs] at h
  have hpositive :
      ∑ b : SecondWeight, (columnTotal packing b : ℤ) *
          (3 + integerDot representativeFunctional (e7Weight4 b.1)) =
        2 * ∑ r : PairIndex,
          (columnTotal packing (positiveColumn r) : ℤ) := by
    calc
      _ = ∑ b : SecondWeight, (columnTotal packing b : ℤ) *
          (2 * if b ∈ positiveColumns then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [representativeFunctional_value]
      _ = 2 * ∑ b : SecondWeight, (columnTotal packing b : ℤ) *
          (if b ∈ positiveColumns then 1 else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by
        apply congrArg (2 * ·)
        exact sum_mul_indicator_list
          (fun b => (columnTotal packing b : ℤ))
          positiveColumns positiveColumns_nodup
  rw [hpositive] at h
  have hz :
      ∑ r : PairIndex,
        (columnTotal packing (positiveColumn r) : ℤ) = 110 := by
    omega
  exact_mod_cast hz

end E7FourEightSpecial
end SRG266
