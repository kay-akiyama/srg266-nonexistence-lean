/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.FullRankGlueVectorBoundary

/-!
# Finite mod-two arithmetic for the index-two glue cases

This module is intentionally isolated: its two plain-kernel reductions inspect
4096 and 16384 residue vectors respectively.  Downstream abstract lattice
proofs import the resulting `.olean` without re-elaborating the finite search.
-/

namespace SRG266
namespace Lattice

set_option maxRecDepth 8000

/-- The reduction of an integer coordinate vector modulo two. -/
def modTwoVector {n : ℕ} (v : Fin n → ℤ) : Fin n → ZMod 2 :=
  fun i => v i

/-- Kernel of a Cartan matrix after reduction modulo two. -/
def InModTwoCartanKernel {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ZMod 2) : Prop :=
  ∀ j, ∑ i, v i * (A i j : ZMod 2) = 0

theorem zmodTwo_mul_two (a : ZMod 2) : a * 2 = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by decide +kernel
  rw [htwo, mul_zero]

theorem zmodTwo_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  have ha : a + a = 0 := by
    linear_combination a * CharP.cast_eq_zero (ZMod 2) 2
  have hb : b + b = 0 := by
    linear_combination b * CharP.cast_eq_zero (ZMod 2) 2
  constructor
  · intro h
    calc
      a = a + 0 := by simp
      _ = a + (b + b) := by rw [hb]
      _ = (a + b) + b := by ac_rfl
      _ = b := by rw [h, zero_add]
  · rintro rfl
    exact ha

theorem zmodTwo_add_add_eq_zero_iff (a b c : ZMod 2) :
    a + (b + c) = 0 ↔ c = a + b := by
  rw [zmodTwo_add_eq_zero_iff]
  have hb : b + b = 0 := by
    linear_combination b * CharP.cast_eq_zero (ZMod 2) 2
  constructor
  · intro h
    calc
      c = 0 + c := by simp
      _ = (b + b) + c := by rw [hb]
      _ = (b + c) + b := by ac_rfl
      _ = a + b := by rw [h]
  · intro h
    calc
      a = 0 + a := by simp
      _ = (b + b) + a := by rw [hb]
      _ = b + (a + b) := by ac_rfl
      _ = b + c := by rw [h]

/-- The other `D12` spinor numerator, obtained by swapping the two terminal
nodes of the Dynkin diagram. -/
def d12OtherGlueNumerator : Fin 12 → ℤ := fun i =>
  if i = 10 then d12GlueNumerator 11
  else if i = 11 then d12GlueNumerator 10
  else d12GlueNumerator i

/-- The vector discriminant class of `D12`. -/
def d12VectorClassNumerator : Fin 12 → ℤ := fun i =>
  if i = 10 ∨ i = 11 then 1 else 0

/-- The two free residues in the `D12` Cartan kernel, written without any
search or matrix inversion. -/
def d12KernelPattern (a b : ZMod 2) : Fin 12 → ZMod 2 := fun i =>
  if i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 6 ∨ i = 8 then a
  else if i = 10 then b
  else if i = 11 then a + b
  else 0

theorem d12KernelPattern_cases (a b : ZMod 2) :
    d12KernelPattern a b = 0 ∨
      d12KernelPattern a b = modTwoVector d12GlueNumerator ∨
      d12KernelPattern a b = modTwoVector d12OtherGlueNumerator ∨
      d12KernelPattern a b = modTwoVector d12VectorClassNumerator := by
  fin_cases a <;> fin_cases b
  · left
    funext i
    fin_cases i <;> decide +kernel
  · right; right; right
    funext i
    fin_cases i <;> decide +kernel
  · right; right; left
    funext i
    fin_cases i <;> decide +kernel
  · right; left
    funext i
    fin_cases i <;> decide +kernel

/-- The four elements of the `D12` discriminant group are exactly the four
vectors listed here. -/
theorem d12_modTwo_kernel_cases :
    ∀ v : Fin 12 → ZMod 2, InModTwoCartanKernel (gramD 12) v →
      v = 0 ∨
        v = modTwoVector d12GlueNumerator ∨
        v = modTwoVector d12OtherGlueNumerator ∨
        v = modTwoVector d12VectorClassNumerator := by
  intro v h
  have h0 := h (0 : Fin 12)
  have h1 := h (1 : Fin 12)
  have h2 := h (2 : Fin 12)
  have h3 := h (3 : Fin 12)
  have h4 := h (4 : Fin 12)
  have h5 := h (5 : Fin 12)
  have h6 := h (6 : Fin 12)
  have h7 := h (7 : Fin 12)
  have h8 := h (8 : Fin 12)
  have h9 := h (9 : Fin 12)
  have h10 := h (10 : Fin 12)
  have h11 := h (11 : Fin 12)
  norm_num [gramD, gramDEntry, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  change v 0 * 2 + v 1 = 0 at h0
  change v 0 + (v 1 * 2 + v 2) = 0 at h1
  change v 1 + (v 2 * 2 + v 3) = 0 at h2
  change v 2 + (v 3 * 2 + v 4) = 0 at h3
  change v 3 + (v 4 * 2 + v 5) = 0 at h4
  change v 4 + (v 5 * 2 + v 6) = 0 at h5
  change v 5 + (v 6 * 2 + v 7) = 0 at h6
  change v 6 + (v 7 * 2 + v 8) = 0 at h7
  change v 7 + (v 8 * 2 + v 9) = 0 at h8
  change v 8 + (v 9 * 2 + (v 10 + v 11)) = 0 at h9
  change v 9 + v 10 * 2 = 0 at h10
  change v 9 + v 11 * 2 = 0 at h11
  have e1 : v 1 = 0 := by
    rw [zmodTwo_mul_two, zero_add] at h0
    exact h0
  have e2 : v 2 = v 0 := by
    rw [e1, zmodTwo_mul_two, zero_add] at h1
    exact (zmodTwo_add_eq_zero_iff _ _).mp h1 |>.symm
  have e3 : v 3 = 0 := by
    rw [e1, zmodTwo_mul_two, zero_add, zero_add] at h2
    exact h2
  have e4 : v 4 = v 0 := by
    rw [e2, e3, zmodTwo_mul_two, zero_add] at h3
    exact (zmodTwo_add_eq_zero_iff _ _).mp h3 |>.symm
  have e5 : v 5 = 0 := by
    rw [e3, zmodTwo_mul_two, zero_add, zero_add] at h4
    exact h4
  have e6 : v 6 = v 0 := by
    rw [e4, e5, zmodTwo_mul_two, zero_add] at h5
    exact (zmodTwo_add_eq_zero_iff _ _).mp h5 |>.symm
  have e7 : v 7 = 0 := by
    rw [e5, zmodTwo_mul_two, zero_add, zero_add] at h6
    exact h6
  have e8 : v 8 = v 0 := by
    rw [e6, e7, zmodTwo_mul_two, zero_add] at h7
    exact (zmodTwo_add_eq_zero_iff _ _).mp h7 |>.symm
  have e9 : v 9 = 0 := by
    rw [e7, zmodTwo_mul_two, zero_add, zero_add] at h8
    exact h8
  have e11 : v 11 = v 0 + v 10 := by
    rw [e8, e9, zmodTwo_mul_two, zero_add] at h9
    exact (zmodTwo_add_add_eq_zero_iff _ _ _).mp h9
  have hv : v = d12KernelPattern (v 0) (v 10) := by
    funext i
    fin_cases i <;>
      simp [d12KernelPattern, e1, e2, e3, e4, e5, e6, e7, e8, e9, e11]
  rw [hv]
  exact d12KernelPattern_cases (v 0) (v 10)

/-- The numerator supported in the first `E7` factor. -/
def e7e7LeftGlueNumerator : Fin 14 → ℤ := fun i =>
  if i.1 < 7 then e7e7GlueNumerator i else 0

/-- The numerator supported in the second `E7` factor. -/
def e7e7RightGlueNumerator : Fin 14 → ℤ := fun i =>
  if 7 ≤ i.1 then e7e7GlueNumerator i else 0

/-- A definitionally rank-14 presentation of the block Cartan matrix.  Keeping
the rank out of a dependent pair makes the coordinate proof below small. -/
def e7e7Cartan : Matrix (Fin 14) (Fin 14) ℤ := fun i j =>
  adeEntry [.E7, .E7] i.1 j.1

theorem e7e7Cartan_eq_adeGram :
    e7e7Cartan = (adeGram [.E7, .E7]).2 := rfl

/-- The two independent `E7` residues in the block Cartan kernel. -/
def e7e7KernelPattern (a b : ZMod 2) : Fin 14 → ZMod 2 := fun i =>
  if i = 3 ∨ i = 5 ∨ i = 6 then a
  else if i = 10 ∨ i = 12 ∨ i = 13 then b
  else 0

theorem e7e7KernelPattern_cases (a b : ZMod 2) :
    e7e7KernelPattern a b = 0 ∨
      e7e7KernelPattern a b = modTwoVector e7e7LeftGlueNumerator ∨
      e7e7KernelPattern a b = modTwoVector e7e7RightGlueNumerator ∨
      e7e7KernelPattern a b = modTwoVector e7e7GlueNumerator := by
  fin_cases a <;> fin_cases b
  · left
    funext i
    fin_cases i <;> decide +kernel
  · right; right; left
    funext i
    fin_cases i <;> decide +kernel
  · right; left
    funext i
    fin_cases i <;> decide +kernel
  · right; right; right
    funext i
    fin_cases i <;> decide +kernel

/-- The four elements of the `(E7 + E7)` discriminant group are obtained by
the two independent one-dimensional factor kernels. -/
theorem e7e7_modTwo_kernel_cases :
    ∀ v : Fin 14 → ZMod 2,
      InModTwoCartanKernel (adeGram [.E7, .E7]).2 v →
        v = 0 ∨
          v = modTwoVector e7e7LeftGlueNumerator ∨
          v = modTwoVector e7e7RightGlueNumerator ∨
          v = modTwoVector e7e7GlueNumerator := by
  intro v h
  change InModTwoCartanKernel e7e7Cartan v at h
  have h0 := h (0 : Fin 14)
  have h1 := h (1 : Fin 14)
  have h2 := h (2 : Fin 14)
  have h3 := h (3 : Fin 14)
  have h4 := h (4 : Fin 14)
  have h5 := h (5 : Fin 14)
  have h6 := h (6 : Fin 14)
  have h7 := h (7 : Fin 14)
  have h8 := h (8 : Fin 14)
  have h9 := h (9 : Fin 14)
  have h10 := h (10 : Fin 14)
  have h11 := h (11 : Fin 14)
  have h12 := h (12 : Fin 14)
  have h13 := h (13 : Fin 14)
  norm_num [e7e7Cartan, adeEntry, ADEType.rank, ADEType.gramEntry, gramEEntry,
    Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  change v 0 * 2 + v 1 = 0 at h0
  change v 0 + (v 1 * 2 + v 2) = 0 at h1
  change v 1 + (v 2 * 2 + (v 3 + v 6)) = 0 at h2
  change v 2 + (v 3 * 2 + v 4) = 0 at h3
  change v 3 + (v 4 * 2 + v 5) = 0 at h4
  change v 4 + v 5 * 2 = 0 at h5
  change v 2 + v 6 * 2 = 0 at h6
  change v 7 * 2 + v 8 = 0 at h7
  change v 7 + (v 8 * 2 + v 9) = 0 at h8
  change v 8 + (v 9 * 2 + (v 10 + v 13)) = 0 at h9
  change v 9 + (v 10 * 2 + v 11) = 0 at h10
  change v 10 + (v 11 * 2 + v 12) = 0 at h11
  change v 11 + v 12 * 2 = 0 at h12
  change v 9 + v 13 * 2 = 0 at h13
  have e1 : v 1 = 0 := by
    rw [zmodTwo_mul_two, zero_add] at h0
    exact h0
  have e2 : v 2 = v 0 := by
    rw [e1, zmodTwo_mul_two, zero_add] at h1
    exact (zmodTwo_add_eq_zero_iff _ _).mp h1 |>.symm
  have e6 : v 6 = v 3 := by
    rw [e1, zmodTwo_mul_two, zero_add, zero_add] at h2
    exact (zmodTwo_add_eq_zero_iff _ _).mp h2 |>.symm
  have e4 : v 4 = v 2 := by
    rw [zmodTwo_mul_two, zero_add] at h3
    exact (zmodTwo_add_eq_zero_iff _ _).mp h3 |>.symm
  have e5 : v 5 = v 3 := by
    rw [zmodTwo_mul_two, zero_add] at h4
    exact (zmodTwo_add_eq_zero_iff _ _).mp h4 |>.symm
  have e4zero : v 4 = 0 := by
    rw [zmodTwo_mul_two, add_zero] at h5
    exact h5
  have e0 : v 0 = 0 := by
    rw [← e2, ← e4]
    exact e4zero
  have e8 : v 8 = 0 := by
    rw [zmodTwo_mul_two, zero_add] at h7
    exact h7
  have e9 : v 9 = v 7 := by
    rw [e8, zmodTwo_mul_two, zero_add] at h8
    exact (zmodTwo_add_eq_zero_iff _ _).mp h8 |>.symm
  have e13 : v 13 = v 10 := by
    rw [e8, zmodTwo_mul_two, zero_add, zero_add] at h9
    exact (zmodTwo_add_eq_zero_iff _ _).mp h9 |>.symm
  have e11 : v 11 = v 9 := by
    rw [zmodTwo_mul_two, zero_add] at h10
    exact (zmodTwo_add_eq_zero_iff _ _).mp h10 |>.symm
  have e12 : v 12 = v 10 := by
    rw [zmodTwo_mul_two, zero_add] at h11
    exact (zmodTwo_add_eq_zero_iff _ _).mp h11 |>.symm
  have e11zero : v 11 = 0 := by
    rw [zmodTwo_mul_two, add_zero] at h12
    exact h12
  have e7 : v 7 = 0 := by
    rw [← e9, ← e11]
    exact e11zero
  have hv : v = e7e7KernelPattern (v 3) (v 10) := by
    funext i
    fin_cases i <;>
      simp [e7e7KernelPattern, e0, e1, e2, e4, e5, e6, e7, e8, e9,
        e11, e12, e13]
  rw [hv]
  exact e7e7KernelPattern_cases (v 3) (v 10)

end Lattice
end SRG266
