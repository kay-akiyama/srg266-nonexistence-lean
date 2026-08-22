/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15CentroidEnumeration
import SRG266.Hosts.A15CentroidSolution

/-!
# Theoretical prerequisites for the A15 centroid enumeration

This module derives the inexpensive mathematical conditions used by the
native canonical-profile search.  In particular:

* a shell realization uses at least 74 distinct eligible four-subsets;
* the centroid coordinates lie in `[-69,69]`;
* after writing `dᵢ = 4aᵢ + r`, the common residue is even.

The last assertion follows from the elementary congruence
`z² = z` in `ZMod 2`; it is not delegated to the profile generator.
-/

open scoped BigOperators

namespace SRG266

set_option maxRecDepth 100000

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every centroid coordinate has square at most the total squared norm. -/
theorem coordinate_sq_le_sum_sq
    (d : Fin 16 → ℤ) (i : Fin 16) :
    d i * d i ≤ ∑ j, d j * d j := by
  classical
  exact
    Finset.single_le_sum
      (fun j _ => mul_self_nonneg (d j))
      (Finset.mem_univ i)

/-- The norm-4800 centroid condition bounds every integral coordinate by
69 in absolute value. -/
theorem A15ShellGramRealization.centroid_coordinate_bounds
    (hG : IsHypothetical G) (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) (i : Fin 16) :
    -69 ≤ d i ∧ d i ≤ 69 := by
  have hnorm := realization.centroid_norm G hG x hdSum
  have hsq := coordinate_sq_le_sum_sq d i
  rw [hnorm] at hsq
  constructor <;> nlinarith

private theorem zmodTwo_mul_self (z : ZMod 2) :
    z * z = z := by
  fin_cases z <;> decide

/-- Parity of a sum of integral squares equals parity of the corresponding
sum. -/
theorem sum_sq_cast_zmodTwo
    (a : Fin 16 → ℤ) :
    (∑ i, (a i : ZMod 2) * (a i : ZMod 2)) =
      ∑ i, (a i : ZMod 2) := by
  apply Finset.sum_congr rfl
  intro i _
  exact zmodTwo_mul_self (a i)

/-- The reduced centroid equations rule out the odd common residue classes.

If `dᵢ = 4aᵢ + r`, coordinate sum zero gives
`∑aᵢ = -4r`, while squared norm 4800 gives
`∑aᵢ² = 300 + r²`.  Reducing both identities modulo two forces `r` to be
even. -/
theorem a15_reduced_residue_even
    (r : ℤ) (a : Fin 16 → ℤ)
    (hsum : ∑ i, a i = -4 * r)
    (hsq : ∑ i, a i * a i = 300 + r * r) :
    r % 2 = 0 := by
  have hsumCast :
      (∑ i, (a i : ZMod 2)) = 0 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 2)) hsum
    calc
      (∑ i, (a i : ZMod 2)) =
          ((-4 * r : ℤ) : ZMod 2) := by
        simpa only [Int.cast_sum] using h
      _ = 0 := by
        push_cast
        rw [show (4 : ZMod 2) = 0 by decide]
        simp
  have hsqCast :
      (∑ i, (a i : ZMod 2) * (a i : ZMod 2)) =
        (r : ZMod 2) * (r : ZMod 2) := by
    have h := congrArg (fun z : ℤ => (z : ZMod 2)) hsq
    calc
      (∑ i, (a i : ZMod 2) * (a i : ZMod 2)) =
          ((300 + r * r : ℤ) : ZMod 2) := by
        simpa only [Int.cast_sum, Int.cast_mul] using h
      _ = (r : ZMod 2) * (r : ZMod 2) := by
        push_cast
        rw [show (300 : ZMod 2) = 0 by decide]
        simp
  have hrCast : (r : ZMod 2) = 0 := by
    rw [sum_sq_cast_zmodTwo a, hsumCast] at hsqCast
    simpa [zmodTwo_mul_self] using hsqCast.symm
  have hdvd : (2 : ℤ) ∣ r :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd r 2).mp hrCast
  exact Int.dvd_iff_emod_eq_zero.mp hdvd

/-- In the normalized residue interval, only residues zero and two remain. -/
theorem a15_reduced_residue_zero_or_two
    (r : ℤ) (a : Fin 16 → ℤ)
    (hr0 : 0 ≤ r) (hr4 : r < 4)
    (hsum : ∑ i, a i = -4 * r)
    (hsq : ∑ i, a i * a i = 300 + r * r) :
    r = 0 ∨ r = 2 := by
  have heven := a15_reduced_residue_even r a hsum hsq
  omega

end SRG266
