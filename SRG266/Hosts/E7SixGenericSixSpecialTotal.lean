/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7SixGenericSixSpecialTheory

/-! # The critical-class total in the residual `6g × 6s` E7 shell -/

open scoped BigOperators Matrix

namespace SRG266
namespace E7SixGenericSixSpecial

open E7SixGenericSixSpecialData

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def criticalTotal (packing : E7ShellPacking d₆g d₆s) : ℕ :=
  ∑ i : CriticalIndex, packing.multiplicity (criticalVertex i)

def criticalNeighbours (i : CriticalIndex) : Finset CriticalIndex :=
  Finset.univ.filter fun j =>
    e7ShellInner (criticalVertex i).1 (criticalVertex j).1 = 2

def globalNeighbours (i : CriticalIndex) : Finset Shell :=
  Finset.univ.filter fun w =>
    e7ShellInner (criticalVertex i).1 w.1 = 2

theorem criticalTotal_eq_fifty_five
    (packing : E7ShellPacking d₆g d₆s) :
    criticalTotal packing = 55 := by
  let critical : Finset Shell :=
    Finset.univ.filter fun w =>
      e7ResidualEvaluation d₆g w.1.1 = 0
  let noncritical : Finset Shell :=
    Finset.univ.filter fun w =>
      ¬e7ResidualEvaluation d₆g w.1.1 = 0
  have haffine := packing.left_affine_sum 0 d₆g
  have haffine_left :
      (∑ w : Shell, (packing.multiplicity w : ℤ) *
          integerDot d₆g (e7Weight4 w.1.1)) =
        16 * ∑ w ∈ noncritical, (packing.multiplicity w : ℤ) := by
    calc
      _ = ∑ w : Shell, (packing.multiplicity w : ℤ) *
          (if e7ResidualEvaluation d₆g w.1.1 = 0 then 0 else 16) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [left_pairing_value]
      _ = 16 * ∑ w ∈ noncritical,
          (packing.multiplicity w : ℤ) := by
        rw [Finset.mul_sum]
        simp only [noncritical, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro w _
        by_cases hw : e7ResidualEvaluation d₆g w.1.1 = 0
        · simp [hw]
        · simp [hw, mul_comm]
  have hnorm : integerDot d₆g d₆g = 24 := by
    rfl
  simp only [zero_add, zero_mul] at haffine
  rw [haffine_left, hnorm] at haffine
  have hnoncriticalZ :
      ∑ w ∈ noncritical, (packing.multiplicity w : ℤ) = 165 := by
    omega
  have hnoncritical :
      ∑ w ∈ noncritical, packing.multiplicity w = 165 := by
    exact_mod_cast hnoncriticalZ
  have hpartition :
      (∑ w ∈ critical, packing.multiplicity w) +
        ∑ w ∈ noncritical, packing.multiplicity w = 220 := by
    have h := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset Shell)
      (fun w => e7ResidualEvaluation d₆g w.1.1 = 0)
      packing.multiplicity
    simp only [critical, noncritical] at h ⊢
    rw [h, packing.total]
  have hcritical :
      ∑ w ∈ critical, packing.multiplicity w = 55 := by
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

end E7SixGenericSixSpecial
end SRG266
