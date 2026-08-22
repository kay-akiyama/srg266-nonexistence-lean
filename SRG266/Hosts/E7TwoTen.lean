/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7TwoTenPSD

/-!
# Exclusion of the residual `2 × 10` E7 shell

The critical label class has 64 shell vectors and total multiplicity 110.
The matrix used by the spectral argument is the sum of the
inner-product-two adjacency matrix, three times the identity, and the
negative-inner-product matching. The matching has zero weighted contribution
on selected vertices. Hence the profile equations give `xᵀ C x = 3300`.

The checked LDLᵀ certificate for `64C - 20J` gives

`64 xᵀ C x ≥ 20 (∑x)²`,

which contradicts `211200 < 242000`.
-/

open scoped BigOperators Matrix

namespace SRG266
namespace E7TwoTen

open E7TwoTenData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def criticalTotal (packing : E7ShellPacking d₂ d₁₀) : ℕ :=
  ∑ i : CriticalIndex, packing.multiplicity (criticalVertex i)

def criticalNeighbours (i : CriticalIndex) : Finset CriticalIndex :=
  Finset.univ.filter fun j =>
    e7ShellInner (criticalVertex i).1 (criticalVertex j).1 = 2

def globalNeighbours (i : CriticalIndex) : Finset Shell :=
  Finset.univ.filter fun w =>
    e7ShellInner (criticalVertex i).1 w.1 = 2

def criticalNegativeNeighbours
    (i : CriticalIndex) : Finset CriticalIndex :=
  Finset.univ.filter fun j =>
    e7ShellInner (criticalVertex i).1 (criticalVertex j).1 = -1

theorem criticalTotal_eq_one_hundred_ten
    (packing : E7ShellPacking d₂ d₁₀) :
    criticalTotal packing = 110 := by
  let critical : Finset Shell :=
    Finset.univ.filter fun w =>
      e7ResidualEvaluation d₂ w.1.1 = 0
  let noncritical : Finset Shell :=
    Finset.univ.filter fun w =>
      ¬e7ResidualEvaluation d₂ w.1.1 = 0
  have haffine := packing.left_affine_sum 0 d₂
  have haffine_left :
      (∑ w : Shell, (packing.multiplicity w : ℤ) *
          integerDot d₂ (e7Weight4 w.1.1)) =
        8 * ∑ w ∈ noncritical, (packing.multiplicity w : ℤ) := by
    calc
      _ = ∑ w : Shell, (packing.multiplicity w : ℤ) *
          (if e7ResidualEvaluation d₂ w.1.1 = 0 then 0 else 8) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [left_pairing_value]
      _ = 8 * ∑ w ∈ noncritical,
          (packing.multiplicity w : ℤ) := by
        rw [Finset.mul_sum]
        simp only [noncritical, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro w _
        by_cases hw : e7ResidualEvaluation d₂ w.1.1 = 0
        · simp [hw]
        · simp [hw, mul_comm]
  have hnorm : integerDot d₂ d₂ = 8 := by
    rfl
  simp only [zero_add, zero_mul] at haffine
  rw [haffine_left, hnorm] at haffine
  have hnoncriticalZ :
      ∑ w ∈ noncritical, (packing.multiplicity w : ℤ) = 110 := by
    omega
  have hnoncritical :
      ∑ w ∈ noncritical, packing.multiplicity w = 110 := by
    exact_mod_cast hnoncriticalZ
  have hpartition :
      (∑ w ∈ critical, packing.multiplicity w) +
        ∑ w ∈ noncritical, packing.multiplicity w = 220 := by
    have h := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset Shell)
      (fun w => e7ResidualEvaluation d₂ w.1.1 = 0)
      packing.multiplicity
    simp only [critical, noncritical] at h ⊢
    rw [h, packing.total]
  have hcritical :
      ∑ w ∈ critical, packing.multiplicity w = 110 := by
    omega
  have hsubtype :
      (∑ w ∈ critical, packing.multiplicity w) =
        ∑ w : CriticalShell, packing.multiplicity w.1 := by
    apply Finset.sum_subtype
    intro w
    simp [critical]
  have hequiv :
      (∑ i : CriticalIndex,
          packing.multiplicity (criticalVertex i)) =
        ∑ w : CriticalShell, packing.multiplicity w.1 := by
    simpa only [criticalEquiv_apply] using
      criticalEquiv.sum_comp
        (fun w : CriticalShell => packing.multiplicity w.1)
  rw [criticalTotal, hequiv, ← hsubtype, hcritical]

theorem critical_neighbour_sum_eq_global
    (packing : E7ShellPacking d₂ d₁₀) (i : CriticalIndex) :
    ∑ j ∈ criticalNeighbours i,
        packing.multiplicity (criticalVertex j) =
      ∑ w ∈ globalNeighbours i, packing.multiplicity w := by
  let critical : Finset Shell :=
    Finset.univ.filter fun w =>
      e7ResidualEvaluation d₂ w.1.1 = 0
  have hequiv :
      (∑ j : CriticalIndex,
          if e7ShellInner (criticalVertex i).1 (criticalVertex j).1 = 2
            then packing.multiplicity (criticalVertex j) else 0) =
        ∑ w : CriticalShell,
          if e7ShellInner (criticalVertex i).1 w.1.1 = 2
            then packing.multiplicity w.1 else 0 := by
    simpa only [criticalEquiv_apply] using
      criticalEquiv.sum_comp
        (fun w : CriticalShell =>
          if e7ShellInner (criticalVertex i).1 w.1.1 = 2
            then packing.multiplicity w.1 else 0)
  have hleft :
      (∑ j ∈ criticalNeighbours i,
          packing.multiplicity (criticalVertex j)) =
        ∑ j : CriticalIndex,
          if e7ShellInner (criticalVertex i).1 (criticalVertex j).1 = 2
            then packing.multiplicity (criticalVertex j) else 0 := by
    rw [criticalNeighbours, Finset.sum_filter]
  have hsubtype :
      (∑ w : CriticalShell,
          if e7ShellInner (criticalVertex i).1 w.1.1 = 2
            then packing.multiplicity w.1 else 0) =
        ∑ w ∈ critical,
          if e7ShellInner (criticalVertex i).1 w.1 = 2
            then packing.multiplicity w else 0 := by
    symm
    apply Finset.sum_subtype
    intro w
    simp [critical]
  have hcritical_filter :
      (∑ w ∈ critical,
          if e7ShellInner (criticalVertex i).1 w.1 = 2
            then packing.multiplicity w else 0) =
        ∑ w ∈ globalNeighbours i, packing.multiplicity w := by
    simp only [critical, globalNeighbours, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hinner : e7ShellInner (criticalVertex i).1 w.1 = 2
    · have hcritical := inner_two_closed i w hinner
      simp [hinner, hcritical]
    · simp [hinner]
  rw [hleft, hequiv, hsubtype, hcritical_filter]

theorem critical_negative_sum_eq_zero
    (packing : E7ShellPacking d₂ d₁₀) (i : CriticalIndex)
    (hi : 0 < packing.multiplicity (criticalVertex i)) :
    ∑ j ∈ criticalNegativeNeighbours i,
      packing.multiplicity (criticalVertex j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  simp only [criticalNegativeNeighbours, Finset.mem_filter,
    Finset.mem_univ, true_and] at hj
  by_contra hm
  have hjpos :
      0 < packing.multiplicity (criticalVertex j) :=
    Nat.pos_of_ne_zero hm
  have hnonnegative :=
    packing.nonnegative (criticalVertex i) (criticalVertex j) hi hjpos
  omega

theorem critical_row_eq_thirty
    (packing : E7ShellPacking d₂ d₁₀) (i : CriticalIndex)
    (hi : 0 < packing.multiplicity (criticalVertex i)) :
    ∑ j : CriticalIndex,
        criticalC i j * packing.multiplicity (criticalVertex j) = 30 := by
  have hprofile := packing.twoProfile (criticalVertex i) hi
  have hneighbours :
      (∑ j : CriticalIndex,
          (if e7ShellInner (criticalVertex i).1 (criticalVertex j).1 = 2
            then 1 else 0) *
            packing.multiplicity (criticalVertex j)) =
        ∑ j ∈ criticalNeighbours i,
          packing.multiplicity (criticalVertex j) := by
    rw [criticalNeighbours, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp_all
  have hdiagonal :
      (∑ j : CriticalIndex, (if i = j then 3 else 0) *
          packing.multiplicity (criticalVertex j)) =
        3 * packing.multiplicity (criticalVertex i) := by
    simp
  have hnegative :
      (∑ j : CriticalIndex,
          (if e7ShellInner (criticalVertex i).1 (criticalVertex j).1 = -1
            then 1 else 0) *
            packing.multiplicity (criticalVertex j)) = 0 := by
    have hzero := critical_negative_sum_eq_zero packing i hi
    rw [criticalNegativeNeighbours, Finset.sum_filter] at hzero
    calc
      _ = ∑ j : CriticalIndex,
          if e7ShellInner (criticalVertex i).1 (criticalVertex j).1 = -1
            then packing.multiplicity (criticalVertex j) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        split <;> simp_all
      _ = 0 := hzero
  simp only [criticalC, add_mul, Finset.sum_add_distrib]
  rw [hneighbours, hdiagonal, hnegative, add_zero,
    critical_neighbour_sum_eq_global packing i]
  simpa only [globalNeighbours] using hprofile

def criticalQuadratic (packing : E7ShellPacking d₂ d₁₀) : ℕ :=
  ∑ i : CriticalIndex,
    packing.multiplicity (criticalVertex i) *
      ∑ j : CriticalIndex,
        criticalC i j * packing.multiplicity (criticalVertex j)

theorem criticalQuadratic_eq
    (packing : E7ShellPacking d₂ d₁₀) :
    criticalQuadratic packing = 30 * criticalTotal packing := by
  rw [criticalQuadratic, criticalTotal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : packing.multiplicity (criticalVertex i) = 0
  · simp [hi]
  · have hpos := Nat.pos_of_ne_zero hi
    rw [critical_row_eq_thirty packing i hpos]
    ring

theorem centered_quadratic_identity
    (packing : E7ShellPacking d₂ d₁₀) :
    rationalQuadraticForm centeredMatrix
        (fun i => (packing.multiplicity (criticalVertex i) : ℚ)) =
      64 * (criticalQuadratic packing : ℚ) -
        20 * (criticalTotal packing : ℚ) ^ 2 := by
  let x : CriticalIndex → ℚ :=
    fun i => (packing.multiplicity (criticalVertex i) : ℚ)
  have hqcast :
      (criticalQuadratic packing : ℚ) =
        ∑ i : CriticalIndex, ∑ j : CriticalIndex,
          x i * criticalC i j * x j := by
    simp only [criticalQuadratic, x]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have htotalcast :
      (criticalTotal packing : ℚ) = ∑ i : CriticalIndex, x i := by
    simp only [criticalTotal, x, Nat.cast_sum]
  have hallones :
      (∑ i : CriticalIndex, ∑ j : CriticalIndex, x i * x j) =
        (∑ i : CriticalIndex, x i) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  change rationalQuadraticForm centeredMatrix x =
    64 * (criticalQuadratic packing : ℚ) -
      20 * (criticalTotal packing : ℚ) ^ 2
  calc
    rationalQuadraticForm centeredMatrix x =
        64 * (∑ i : CriticalIndex, ∑ j : CriticalIndex,
          x i * criticalC i j * x j) -
        20 * (∑ i : CriticalIndex, ∑ j : CriticalIndex,
          x i * x j) := by
      simp only [rationalQuadraticForm, centeredMatrix, centeredInt]
      calc
        _ = ∑ i : CriticalIndex, ∑ j : CriticalIndex,
            (64 * (x i * criticalC i j * x j) -
              20 * (x i * x j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          push_cast
          ring
        _ = _ := by
          calc
            _ = ∑ i : CriticalIndex, (
                (64 * ∑ j : CriticalIndex,
                    x i * criticalC i j * x j) -
                  20 * ∑ j : CriticalIndex, x i * x j) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
                ← Finset.mul_sum]
            _ = _ := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
                ← Finset.mul_sum]
    _ = _ := by rw [← hqcast, hallones, ← htotalcast]

/-- The residual `2 × 10` shell cannot contain the required packing. -/
theorem no_packing : IsEmpty (E7ShellPacking d₂ d₁₀) := by
  refine ⟨fun packing => ?_⟩
  have hpsd := rationalQuadraticForm_nonnegative_of_ldlt
    centeredMatrix ldltLower ldltDiagonal
    centeredMatrix_ldlt_checked
    (fun i => (packing.multiplicity (criticalVertex i) : ℚ))
  rw [centered_quadratic_identity packing,
    criticalQuadratic_eq packing,
    criticalTotal_eq_one_hundred_ten packing] at hpsd
  norm_num at hpsd

end E7TwoTen
end SRG266
