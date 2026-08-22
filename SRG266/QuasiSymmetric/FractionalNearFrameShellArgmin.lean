/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.FractionalNearFrameAudit

/-!
# Semantic shell argmins for fractional near frames

Canonical Farkas normalization computes a minimum by enumerating every column
in every endpoint shell.  This module isolates the mathematical content of
that computation: it is enough to construct one least column, or merely a
certified integer lower bound, in each shell.  The endpoint weights are then
reconstructed from those bounds, and Farkas soundness uses only their universal
lower-bound property.

This interface is intended for structural shell classifications and local
exchange arguments.  It contains no stored separator or shell certificate.
-/

namespace SRG266.QuasiSymmetric

/-- A chosen mathematical column is least for the given pair functional in
its endpoint shell. -/
def IsCompactPairShellArgmin (nearMask : ℕ)
    (pairWeight : ℕ × ℕ → ℤ) (endpoint : CompactEndpointIndex nearMask)
    (chosen : ℕ) : Prop :=
  IsCompactNearColumn nearMask (compactEndpointMaskAt nearMask endpoint) chosen ∧
    ∀ column,
      IsCompactNearColumn nearMask
          (compactEndpointMaskAt nearMask endpoint) column →
        compactKernelPairWeightSum nearMask pairWeight chosen ≤
          compactKernelPairWeightSum nearMask pairWeight column

/-- Normalization weights reconstructed from one semantic argmin per shell. -/
def compactShellArgminEndpointWeights (nearMask : ℕ)
    (pairWeight : ℕ × ℕ → ℤ)
    (chosen : CompactEndpointIndex nearMask → ℕ) : Array ℤ :=
  Array.ofFn fun endpoint =>
    -compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
      compactKernelPairWeightSum nearMask pairWeight (chosen endpoint)

@[simp] theorem compactWitnessAt_shellArgminEndpointWeights
    (nearMask : ℕ) (pairWeight : ℕ × ℕ → ℤ)
    (chosen : CompactEndpointIndex nearMask → ℕ)
    (endpoint : CompactEndpointIndex nearMask) :
    compactWitnessAt
        (compactShellArgminEndpointWeights nearMask pairWeight chosen)
        endpoint.val =
      -compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
        compactKernelPairWeightSum nearMask pairWeight (chosen endpoint) := by
  simp [compactShellArgminEndpointWeights, compactWitnessAt, Array.getD,
    endpoint.isLt]

/-- Semantic shell argmins turn a pair functional into a Farkas obstruction.
No executable shell minimum occurs in either premise. -/
theorem noCompactFractionalNearFrame_of_shellArgmins
    (nearMask : ℕ) (pairWeight : ℕ × ℕ → ℤ)
    (chosen : CompactEndpointIndex nearMask → ℕ)
    (hargmin : ∀ endpoint,
      IsCompactPairShellArgmin nearMask pairWeight endpoint (chosen endpoint))
    (hrhs : compactFunctionalFarkasRhsDot nearMask
      (compactShellArgminEndpointWeights nearMask pairWeight chosen)
      pairWeight < 0) :
    NoCompactFractionalNearFrame nearMask := by
  apply SRG266.no_nonnegative_rational_solution_of_integer_farkas
    (compactFractionalMatrix nearMask) (compactFractionalRhs nearMask)
    (compactFunctionalFarkasVector nearMask
      (compactShellArgminEndpointWeights nearMask pairWeight chosen) pairWeight)
  constructor
  · intro column
    rw [integerDot_compactFunctionalFarkasVector_matrixColumn,
      ← compactKernelFunctionalFarkasColumnSlack_eq]
    rw [compactKernelFunctionalFarkasColumnSlack,
      compactWitnessAt_shellArgminEndpointWeights]
    change 0 ≤
      -compactEndpointCoefficient
          (compactEndpointMaskAt nearMask column.1) *
          compactKernelPairWeightSum nearMask pairWeight (chosen column.1) +
        compactEndpointCoefficient
          (compactEndpointMaskAt nearMask column.1) *
          compactKernelPairWeightSum nearMask pairWeight column.2.1
    have hminimum := (hargmin column.1).2 column.2.1 column.2.2
    have hcoefficient :
        0 ≤ compactEndpointCoefficient
          (compactEndpointMaskAt nearMask column.1) := by
      simp only [compactEndpointCoefficient]
      split <;> norm_num
    nlinarith [mul_le_mul_of_nonneg_left hminimum hcoefficient]
  · rw [integerDot_compactFunctionalFarkasVector_rhs]
    exact hrhs

/-! ## Indexed pair weights from shell lower bounds -/

private theorem foldl_add_eq_add_sum_map {α : Type*}
    (value : α → ℤ) (items : List α) (base : ℤ) :
    items.foldl (fun total item => total + value item) base =
      base + (items.map value).sum := by
  induction items generalizing base with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons]
      ring

private theorem foldl_add_eq_sum_map {α : Type*}
    (value : α → ℤ) (items : List α) :
    items.foldl (fun total item => total + value item) 0 =
      (items.map value).sum := by
  rw [foldl_add_eq_add_sum_map]
  simp

/-- A per-endpoint lower bound on the indexed pair weight over an endpoint shell.
The lower bound is independent of a chosen concrete column and is therefore the
smallest API needed for the Farkas obstruction argument. -/
def IsCompactIndexedPairShellLowerBound (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask) (lowerBound : ℤ) : Prop :=
  ∀ column,
    IsCompactNearColumn nearMask (compactEndpointMaskAt nearMask endpoint) column →
      lowerBound ≤ compactKernelIndexedPairWeightSum nearMask witness column

/-- Endpoint weight reconstructed from a per-endpoint lower bound. -/
def compactIndexedShellLowerBoundEndpointWeight (nearMask : ℕ)
    (lowerBound : CompactEndpointIndex nearMask → ℤ)
    (endpoint : CompactEndpointIndex nearMask) : ℤ :=
  -compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
    lowerBound endpoint

/-- Indexed Farkas vector reconstructed from one lower bound per shell. -/
def compactIndexedShellLowerBoundFarkasVector (nearMask : ℕ)
    (witness : Array ℤ) (lowerBound : CompactEndpointIndex nearMask → ℤ) :
    CompactFractionalRow nearMask → ℤ
  | .inl endpoint =>
      compactIndexedShellLowerBoundEndpointWeight nearMask lowerBound endpoint
  | .inr pair => compactWitnessAt witness pair.val

/-- Exact right-hand side of the lower-bound indexed shell vector. -/
def compactIndexedShellLowerBoundFarkasRhsDot (nearMask : ℕ)
    (witness : Array ℤ) (lowerBound : CompactEndpointIndex nearMask → ℤ) : ℤ :=
  (∑ endpoint : CompactEndpointIndex nearMask,
      compactIndexedShellLowerBoundEndpointWeight nearMask lowerBound endpoint) +
    3 * ∑ pair : CompactPairIndex nearMask,
      compactWitnessAt witness pair.val

/-- Kernel-oriented right-hand side without shell-minimum enumeration. -/
def compactKernelIndexedShellLowerBoundFarkasRhsDot (nearMask : ℕ)
    (witness : Array ℤ) (lowerBound : CompactEndpointIndex nearMask → ℤ) : ℤ :=
  (List.ofFn fun endpoint : CompactEndpointIndex nearMask => endpoint).foldl
      (fun total endpoint => total +
        compactIndexedShellLowerBoundEndpointWeight nearMask lowerBound endpoint) 0 +
    3 * (List.range (compactIntersectionOnePairs nearMask).length).foldl
      (fun total pairIndex => total + compactWitnessAt witness pairIndex) 0

theorem compactKernelIndexedShellLowerBoundFarkasRhsDot_eq
    (nearMask : ℕ) (witness : Array ℤ)
    (lowerBound : CompactEndpointIndex nearMask → ℤ) :
    compactKernelIndexedShellLowerBoundFarkasRhsDot nearMask witness lowerBound =
      compactIndexedShellLowerBoundFarkasRhsDot nearMask witness lowerBound := by
  rw [compactKernelIndexedShellLowerBoundFarkasRhsDot,
    compactIndexedShellLowerBoundFarkasRhsDot, foldl_add_eq_sum_map,
    foldl_add_eq_sum_map,
    list_sum_map_range_eq_sum_fin]
  rw [List.map_ofFn, List.sum_ofFn]
  simp

theorem integerDot_compactIndexedShellLowerBoundFarkasVector_matrixColumn
    (nearMask : ℕ) (witness : Array ℤ)
    (lowerBound : CompactEndpointIndex nearMask → ℤ)
    (column : CompactFractionalColumn nearMask) :
    SRG266.integerDot
        (compactIndexedShellLowerBoundFarkasVector nearMask witness lowerBound)
        (fun row => compactFractionalMatrix nearMask row column) =
      compactIndexedShellLowerBoundEndpointWeight nearMask lowerBound column.1 +
        compactEndpointCoefficient (compactEndpointMaskAt nearMask column.1) *
          compactIndexedPairWeightSum nearMask witness column.2.1 := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type,
    compactIndexedShellLowerBoundFarkasVector, compactFractionalMatrix,
    compactIndexedPairWeightSum]
  rw [Finset.sum_eq_single column.1]
  · simp only [if_pos, mul_one]
    rw [Finset.mul_sum]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro pair _
    split_ifs <;>
      (simp_all [compactIntersectionOnePairAt] <;> ring)
  · intro endpoint _ hne
    simp [hne]
  · simp

theorem integerDot_compactIndexedShellLowerBoundFarkasVector_rhs
    (nearMask : ℕ) (witness : Array ℤ)
    (lowerBound : CompactEndpointIndex nearMask → ℤ) :
    SRG266.integerDot
        (compactIndexedShellLowerBoundFarkasVector nearMask witness lowerBound)
        (compactFractionalRhs nearMask) =
      compactIndexedShellLowerBoundFarkasRhsDot nearMask witness lowerBound := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type,
    compactIndexedShellLowerBoundFarkasVector, compactFractionalRhs,
    compactIndexedShellLowerBoundFarkasRhsDot, mul_one]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro pair _
  ring

/-- Lower bounds per shell are enough for indexed Farkas obstructions. -/
theorem noCompactFractionalNearFrame_of_indexedShellLowerBounds
    (nearMask : ℕ) (witness : Array ℤ)
    (lowerBound : CompactEndpointIndex nearMask → ℤ)
    (hbound : ∀ endpoint, IsCompactIndexedPairShellLowerBound
      nearMask witness endpoint (lowerBound endpoint))
    (hrhs : compactKernelIndexedShellLowerBoundFarkasRhsDot nearMask witness lowerBound < 0) :
    NoCompactFractionalNearFrame nearMask := by
  apply SRG266.no_nonnegative_rational_solution_of_integer_farkas
    (compactFractionalMatrix nearMask) (compactFractionalRhs nearMask)
    (compactIndexedShellLowerBoundFarkasVector nearMask witness lowerBound)
  constructor
  · intro column
    rw [integerDot_compactIndexedShellLowerBoundFarkasVector_matrixColumn,
      ← compactKernelIndexedPairWeightSum_eq]
    rw [compactIndexedShellLowerBoundEndpointWeight]
    have hminimum := (hbound column.1) column.2.1 column.2.2
    have hcoefficient :
        0 ≤ compactEndpointCoefficient
          (compactEndpointMaskAt nearMask column.1) := by
      simp only [compactEndpointCoefficient]
      split <;> norm_num
    nlinarith [mul_le_mul_of_nonneg_left hminimum hcoefficient]
  · rw [integerDot_compactIndexedShellLowerBoundFarkasVector_rhs,
      ← compactKernelIndexedShellLowerBoundFarkasRhsDot_eq]
    exact hrhs

end SRG266.QuasiSymmetric
