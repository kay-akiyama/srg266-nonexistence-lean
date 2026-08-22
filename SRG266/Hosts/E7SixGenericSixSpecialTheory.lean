/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7SixGenericSixSpecialPSDBijective
import SRG266.Certificates.E7SixGenericSixSpecialPSDInner
import SRG266.Certificates.E7SixGenericSixSpecialPSDPairing
import Mathlib.Algebra.Order.Chebyshev

/-!
# Structural PSD bound for the residual E7 `6g × 6s` shell

The twenty critical shell vectors are two copies of the ten edges of `K₅`.
After adding and subtracting the two copies, the centered quadratic form is a
sum of a variance term and an edge-incidence term.  This gives its
nonnegativity without the generated `20 × 20` LDLᵀ audit.
-/

open scoped BigOperators Matrix

namespace SRG266
namespace E7SixGenericSixSpecialData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def criticalAt (b : Fin 2) (e : Fin 10) : CriticalIndex :=
  finProdFinEquiv (b, e)

private theorem criticalAt_bijective :
    Function.Bijective (fun p : Fin 2 × Fin 10 => criticalAt p.1 p.2) := by
  decide +kernel

private noncomputable def criticalBlockEquiv :
    Fin 2 × Fin 10 ≃ CriticalIndex :=
  Equiv.ofBijective (fun p => criticalAt p.1 p.2) criticalAt_bijective

@[simp] private theorem criticalBlockEquiv_apply (p : Fin 2 × Fin 10) :
    criticalBlockEquiv p = criticalAt p.1 p.2 := by
  rfl

private def edgeLeft : Fin 10 → Fin 5 :=
  ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3]

private def edgeRight : Fin 10 → Fin 5 :=
  ![1, 2, 3, 4, 2, 3, 4, 3, 4, 4]

private def edgeIncidence (v : Fin 5) (e : Fin 10) : ℚ :=
  if v = edgeLeft e ∨ v = edgeRight e then 1 else 0

private def edgeGram (e f : Fin 10) : ℚ :=
  ∑ v : Fin 5, edgeIncidence v e * edgeIncidence v f

private def diagonalKernel (e f : Fin 10) : ℚ :=
  if e = f then 1 else 0

private def sameKernel (e f : Fin 10) : ℚ :=
  edgeGram e f + diagonalKernel e f

private def crossKernel (e f : Fin 10) : ℚ :=
  1 + diagonalKernel e f - edgeGram e f

private def kernelBilinear (K : Fin 10 → Fin 10 → ℚ)
    (u v : Fin 10 → ℚ) : ℚ :=
  ∑ e : Fin 10, ∑ f : Fin 10, u e * K e f * v f

private def symmetricPart (x : CriticalIndex → ℚ) (e : Fin 10) : ℚ :=
  x (criticalAt 0 e) + x (criticalAt 1 e)

private def antisymmetricPart (x : CriticalIndex → ℚ) (e : Fin 10) : ℚ :=
  x (criticalAt 0 e) - x (criticalAt 1 e)

private def incidenceFlow (u : Fin 10 → ℚ) (v : Fin 5) : ℚ :=
  ∑ e : Fin 10, edgeIncidence v e * u e

private def vertexFlow (x : CriticalIndex → ℚ) (v : Fin 5) : ℚ :=
  incidenceFlow (antisymmetricPart x) v

private theorem sum_critical_reindex (f : CriticalIndex → ℚ) :
    (∑ i : CriticalIndex, f i) =
      ∑ b : Fin 2, ∑ e : Fin 10, f (criticalAt b e) := by
  have h := criticalBlockEquiv.sum_comp f
  rw [Fintype.sum_prod_type] at h
  exact h.symm

private theorem criticalC_reindex (b c : Fin 2) (e f : Fin 10) :
    (criticalC (criticalAt b e) (criticalAt c f) : ℚ) =
      if b = c then sameKernel e f else crossKernel e f := by
  fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
    decide +kernel

private theorem criticalQuadratic_block_decomposition
    (x : CriticalIndex → ℚ) :
    (∑ i : CriticalIndex, ∑ j : CriticalIndex,
        x i * criticalC i j * x j) =
      kernelBilinear sameKernel
          (fun e => x (criticalAt 0 e)) (fun e => x (criticalAt 0 e)) +
        kernelBilinear crossKernel
          (fun e => x (criticalAt 0 e)) (fun e => x (criticalAt 1 e)) +
        kernelBilinear crossKernel
          (fun e => x (criticalAt 1 e)) (fun e => x (criticalAt 0 e)) +
        kernelBilinear sameKernel
          (fun e => x (criticalAt 1 e)) (fun e => x (criticalAt 1 e)) := by
  rw [sum_critical_reindex]
  simp_rw [sum_critical_reindex]
  simp only [Fin.sum_univ_two, criticalC_reindex, if_pos, Fin.zero_ne_one,
    one_ne_zero, if_false, kernelBilinear]
  simp_rw [Finset.sum_add_distrib]
  ring

private theorem kernelBilinear_add (K L : Fin 10 → Fin 10 → ℚ)
    (u v : Fin 10 → ℚ) :
    kernelBilinear (fun e f => K e f + L e f) u v =
      kernelBilinear K u v + kernelBilinear L u v := by
  unfold kernelBilinear
  calc
    _ = ∑ e : Fin 10, ∑ f : Fin 10,
        (u e * K e f * v f + u e * L e f * v f) := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro f _
      ring
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]

private theorem kernelBilinear_sub (K L : Fin 10 → Fin 10 → ℚ)
    (u v : Fin 10 → ℚ) :
    kernelBilinear (fun e f => K e f - L e f) u v =
      kernelBilinear K u v - kernelBilinear L u v := by
  unfold kernelBilinear
  calc
    _ = ∑ e : Fin 10, ∑ f : Fin 10,
        (u e * K e f * v f - u e * L e f * v f) := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro f _
      ring
    _ = _ := by
      simp_rw [Finset.sum_sub_distrib]

private theorem kernelBilinear_one (u v : Fin 10 → ℚ) :
    kernelBilinear (fun _ _ => 1) u v =
      (∑ e : Fin 10, u e) * ∑ f : Fin 10, v f := by
  unfold kernelBilinear
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  ring

private theorem kernelBilinear_diagonal (u v : Fin 10 → ℚ) :
    kernelBilinear diagonalKernel u v =
      ∑ e : Fin 10, u e * v e := by
  classical
  simp [kernelBilinear, diagonalKernel]

private theorem kernelBilinear_same (u v : Fin 10 → ℚ) :
    kernelBilinear sameKernel u v =
      kernelBilinear edgeGram u v + ∑ e : Fin 10, u e * v e := by
  rw [show sameKernel = fun e f => edgeGram e f + diagonalKernel e f by rfl,
    kernelBilinear_add, kernelBilinear_diagonal]

private theorem kernelBilinear_cross (u v : Fin 10 → ℚ) :
    kernelBilinear crossKernel u v =
      (∑ e : Fin 10, u e) * (∑ f : Fin 10, v f) +
        (∑ e : Fin 10, u e * v e) - kernelBilinear edgeGram u v := by
  rw [show crossKernel = fun e f =>
      ((fun _ _ => (1 : ℚ)) e f + diagonalKernel e f) - edgeGram e f by
        funext e f
        rfl,
    kernelBilinear_sub, kernelBilinear_add, kernelBilinear_one,
    kernelBilinear_diagonal]

private theorem kernelBilinear_edgeGram (u v : Fin 10 → ℚ) :
    kernelBilinear edgeGram u v =
      ∑ a : Fin 5, incidenceFlow u a * incidenceFlow v a := by
  simp only [kernelBilinear, edgeGram, incidenceFlow,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring

private theorem incidenceFlow_sub (u v : Fin 10 → ℚ) (a : Fin 5) :
    incidenceFlow (fun e => u e - v e) a =
      incidenceFlow u a - incidenceFlow v a := by
  unfold incidenceFlow
  calc
    _ = ∑ e : Fin 10,
        (edgeIncidence a e * u e - edgeIncidence a e * v e) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib]

private theorem blockKernel_quadratic_structural (u v : Fin 10 → ℚ) :
    kernelBilinear sameKernel u u + kernelBilinear crossKernel u v +
        kernelBilinear crossKernel v u + kernelBilinear sameKernel v v =
      (∑ a : Fin 5,
          (incidenceFlow (fun e => u e - v e) a) ^ 2) +
        (∑ e : Fin 10, (u e + v e) ^ 2) +
        (((∑ e : Fin 10, (u e + v e)) ^ 2 -
          (∑ e : Fin 10, (u e - v e)) ^ 2) / 2) := by
  have hedge :
      (∑ a : Fin 5,
          (incidenceFlow (fun e => u e - v e) a) ^ 2) =
        kernelBilinear edgeGram u u - kernelBilinear edgeGram u v -
          kernelBilinear edgeGram v u + kernelBilinear edgeGram v v := by
    calc
      _ = ∑ a : Fin 5,
          (incidenceFlow u a * incidenceFlow u a -
            incidenceFlow u a * incidenceFlow v a -
            incidenceFlow v a * incidenceFlow u a +
            incidenceFlow v a * incidenceFlow v a) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [incidenceFlow_sub]
        ring
      _ = (∑ a : Fin 5, incidenceFlow u a * incidenceFlow u a) -
          (∑ a : Fin 5, incidenceFlow u a * incidenceFlow v a) -
          (∑ a : Fin 5, incidenceFlow v a * incidenceFlow u a) +
          ∑ a : Fin 5, incidenceFlow v a * incidenceFlow v a := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = _ := by
        rw [← kernelBilinear_edgeGram, ← kernelBilinear_edgeGram,
          ← kernelBilinear_edgeGram, ← kernelBilinear_edgeGram]
  have hdiagonal :
      (∑ e : Fin 10, (u e + v e) ^ 2) =
        (∑ e : Fin 10, u e * u e) + (∑ e : Fin 10, u e * v e) +
          (∑ e : Fin 10, v e * u e) + ∑ e : Fin 10, v e * v e := by
    calc
      _ = ∑ e : Fin 10,
          (u e * u e + u e * v e + v e * u e + v e * v e) := by
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = _ := by simp_rw [Finset.sum_add_distrib]
  have hplus :
      (∑ e : Fin 10, (u e + v e)) =
        (∑ e : Fin 10, u e) + ∑ e : Fin 10, v e := by
    rw [Finset.sum_add_distrib]
  have hminus :
      (∑ e : Fin 10, (u e - v e)) =
        (∑ e : Fin 10, u e) - ∑ e : Fin 10, v e := by
    rw [Finset.sum_sub_distrib]
  rw [kernelBilinear_same, kernelBilinear_cross,
    kernelBilinear_cross, kernelBilinear_same]
  rw [hedge, hdiagonal, hplus, hminus]
  ring

/-- The uncentered critical quadratic form is the sum of an incidence energy,
the symmetric-coordinate norm, and one difference of squared totals. -/
theorem criticalQuadratic_structural (x : CriticalIndex → ℚ) :
    (∑ i : CriticalIndex, ∑ j : CriticalIndex,
        x i * criticalC i j * x j) =
      (∑ v : Fin 5, (vertexFlow x v) ^ 2) +
        (∑ e : Fin 10, (symmetricPart x e) ^ 2) +
        (((∑ e : Fin 10, symmetricPart x e) ^ 2 -
          (∑ e : Fin 10, antisymmetricPart x e) ^ 2) / 2) := by
  rw [criticalQuadratic_block_decomposition,
    blockKernel_quadratic_structural]
  rfl

private theorem sum_critical_eq_symmetric (x : CriticalIndex → ℚ) :
    (∑ i : CriticalIndex, x i) =
      ∑ e : Fin 10, symmetricPart x e := by
  rw [sum_critical_reindex, Fin.sum_univ_two]
  unfold symmetricPart
  rw [Finset.sum_add_distrib]

private theorem sum_edgeIncidence (e : Fin 10) :
    (∑ v : Fin 5, edgeIncidence v e) = 2 := by
  fin_cases e <;> decide +kernel

private theorem sum_vertexFlow_eq (x : CriticalIndex → ℚ) :
    (∑ v : Fin 5, vertexFlow x v) =
      2 * ∑ e : Fin 10, antisymmetricPart x e := by
  unfold vertexFlow incidenceFlow
  rw [Finset.sum_comm]
  calc
    _ = ∑ e : Fin 10,
        (∑ v : Fin 5, edgeIncidence v e) * antisymmetricPart x e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_mul]
    _ = _ := by
      simp_rw [sum_edgeIncidence]
      rw [← Finset.mul_sum]

/-- The centered critical form is nonnegative by Cauchy--Schwarz on the ten
edge coordinates and on the five vertex-incidence sums. -/
theorem criticalCentered_nonnegative (x : CriticalIndex → ℚ) :
    0 ≤ 20 * (∑ i : CriticalIndex, ∑ j : CriticalIndex,
        x i * criticalC i j * x j) -
      12 * (∑ i : CriticalIndex, x i) ^ 2 := by
  have hsymmetric := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin 10)))
    (f := symmetricPart x)
  have hflow := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin 5)))
    (f := vertexFlow x)
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hsymmetric hflow
  rw [sum_vertexFlow_eq] at hflow
  rw [criticalQuadratic_structural, sum_critical_eq_symmetric]
  nlinarith [sq_nonneg (∑ e : Fin 10, symmetricPart x e),
    sq_nonneg (∑ e : Fin 10, antisymmetricPart x e)]

end E7SixGenericSixSpecialData
end SRG266
