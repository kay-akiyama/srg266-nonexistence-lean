/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.CoordinateRationalLattice
import SRG266.Lattice.Glue
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The standard rational lattice

This file packages the ordinary dot product on `Q^m` and proves that the
coordinate copy of `Z^m` is a positive-definite self-dual lattice.  These are
the right-hand summands in the rank-24 stabilization.
-/

namespace SRG266.Lattice

open scoped BigOperators

/-- The ordinary dot product on `Q^m`, as a rational bilinear form. -/
def standardRatForm (m : ℕ) : LinearMap.BilinForm ℚ (Fin m → ℚ) :=
  dotProductBilin ℚ ℚ

@[simp]
theorem standardRatForm_apply {m : ℕ} (x y : Fin m → ℚ) :
    standardRatForm m x y = ∑ i, x i * y i :=
  rfl

theorem standardRatForm_isSymm (m : ℕ) : (standardRatForm m).IsSymm := by
  constructor
  intro x y
  simp only [standardRatForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem standardRatForm_posDef (m : ℕ) :
    ∀ x : Fin m → ℚ, x ≠ 0 → 0 < standardRatForm m x x := by
  intro x hx
  have hex : ∃ i, x i ≠ 0 := by
    simpa only [Function.ne_iff, Pi.zero_apply] using hx
  obtain ⟨i, hi⟩ := hex
  rw [standardRatForm_apply]
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg (x j))
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

/-- The standard coordinate lattice is self-dual for the dot product. -/
theorem standardRatForm_dual_coordinateIntegerLattice (m : ℕ) :
    (standardRatForm m).dualSubmodule (coordinateIntegerLattice m) =
      coordinateIntegerLattice m := by
  ext x
  constructor
  · intro hx
    let z : Fin m → ℤ := fun i =>
      (mem_one_iff.mp (hx (intCoordsToRat (Pi.single i 1))
        (intCoordsToRat_mem (Pi.single i 1)))).choose
    refine mem_coordinateIntegerLattice.mpr ⟨z, ?_⟩
    intro i
    have hi := (mem_one_iff.mp (hx (intCoordsToRat (Pi.single i 1))
      (intCoordsToRat_mem (Pi.single i 1)))).choose_spec
    change ((z i : ℤ) : ℚ) = x i
    calc
      ((z i : ℤ) : ℚ) = standardRatForm m x
          (intCoordsToRat (Pi.single i 1)) := hi
      _ = x i := by
        rw [standardRatForm_apply, Finset.sum_eq_single i]
        · simp [intCoordsToRat]
        · intro j _ hji
          simp [intCoordsToRat, hji]
        · exact fun hiu => absurd (Finset.mem_univ i) hiu
  · intro hx y hy
    obtain ⟨a, ha⟩ := mem_coordinateIntegerLattice.mp hx
    obtain ⟨b, hb⟩ := mem_coordinateIntegerLattice.mp hy
    apply mem_one_iff.mpr
    refine ⟨∑ i, a i * b i, ?_⟩
    rw [standardRatForm_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [ha i, hb i]

end SRG266.Lattice
