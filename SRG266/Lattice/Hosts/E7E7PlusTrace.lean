/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Hosts.E7E7PlusTraceChecks

/-!
# Trace vectors in the glued E7 pair

This module isolates the eight trace vectors used by the projector bound in
the pure E7 branch.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators Matrix

/-! ## The eight trace vectors of one factor -/

theorem e7e7PlusTraceVector_block (side : Bool) (i j : Fin 8) :
    e7e7PlusBlock side (e7e7PlusTraceCoeff side i) j = e7TraceRow i j := by
  rw [e7e7PlusBlock]
  cases side
  · exact e7e7PlusTraceCoeff_vecMul false i (Sum.inl j)
  · exact e7e7PlusTraceCoeff_vecMul true i (Sum.inr j)

/-- **Pairing against a trace vector reads a block coordinate.**  Because the
block sums vanish, `⟨8 e_i - 1, w⟩ = 8 w_i`, which in scaled coordinates is
twice the `i`-th block coordinate. -/
theorem e7e7PlusTrace_toBilin' (side : Bool) (i : Fin 8) (w : Fin 14 → ℤ) :
    Matrix.toBilin' e7e7PlusGram (e7e7PlusTraceCoeff side i) w =
      2 * e7e7PlusBlock side w i := by
  have hdot := dotProduct_vecMul_coords e7e7PlusGram e7e7PlusCoords 4 e7e7PlusCoords_gram
    (e7e7PlusTraceCoeff side i) w
  have hsplit : dotProduct (Matrix.vecMul (e7e7PlusTraceCoeff side i) e7e7PlusCoords)
      (Matrix.vecMul w e7e7PlusCoords) =
        ∑ j, e7TraceRow i j * e7e7PlusBlock side w j := by
    rw [dotProduct, Fintype.sum_sum_type]
    cases side
    · rw [Finset.sum_congr rfl fun j _ =>
        show Matrix.vecMul (e7e7PlusTraceCoeff false i) e7e7PlusCoords (Sum.inr j) *
            Matrix.vecMul w e7e7PlusCoords (Sum.inr j) = 0 by
          rw [e7e7PlusTraceCoeff_vecMul false i (Sum.inr j)]
          simp [e7e7PlusTraceVector]]
      simp only [Finset.sum_const, smul_zero, add_zero]
      exact Finset.sum_congr rfl fun j _ => by
        rw [e7e7PlusTraceCoeff_vecMul false i (Sum.inl j)]
        rfl
    · rw [Finset.sum_congr rfl fun j _ =>
        show Matrix.vecMul (e7e7PlusTraceCoeff true i) e7e7PlusCoords (Sum.inl j) *
            Matrix.vecMul w e7e7PlusCoords (Sum.inl j) = 0 by
          rw [e7e7PlusTraceCoeff_vecMul true i (Sum.inl j)]
          simp [e7e7PlusTraceVector]]
      simp only [Finset.sum_const, smul_zero, zero_add]
      exact Finset.sum_congr rfl fun j _ => by
        rw [e7e7PlusTraceCoeff_vecMul true i (Sum.inr j)]
        rfl
  have hrow : ∑ j, e7TraceRow i j * e7e7PlusBlock side w j =
      32 * e7e7PlusBlock side w i - 4 * ∑ j, e7e7PlusBlock side w j := by
    have hpoint : ∀ j, e7TraceRow i j * e7e7PlusBlock side w j =
        (if j = i then 32 * e7e7PlusBlock side w i else 0) - 4 * e7e7PlusBlock side w j := by
      intro j
      rw [e7TraceRow]
      by_cases hj : j = i
      · rw [if_pos hj, if_pos hj, hj]; ring
      · rw [if_neg hj, if_neg hj]; ring
    rw [Finset.sum_congr rfl fun j _ => hpoint j, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ i (fun _ => 32 * e7e7PlusBlock side w i),
      if_pos (Finset.mem_univ i), ← Finset.mul_sum]
  rw [hsplit, hrow, e7e7PlusBlock_sum side w] at hdot
  have h : 32 * e7e7PlusBlock side w i =
      16 * Matrix.toBilin' e7e7PlusGram (e7e7PlusTraceCoeff side i) w := by
    have h16 : (4 : ℤ) ^ 2 = 16 := by norm_num
    rw [h16] at hdot
    omega
  omega

/-- Every trace vector has norm `56`. -/
theorem e7e7PlusTrace_norm (side : Bool) (i : Fin 8) :
    Matrix.toBilin' e7e7PlusGram (e7e7PlusTraceCoeff side i)
      (e7e7PlusTraceCoeff side i) = 56 := by
  rw [e7e7PlusTrace_toBilin' side i, e7e7PlusTraceVector_block side i i, e7TraceRow,
    if_pos rfl]
  norm_num

end Lattice
end SRG266

