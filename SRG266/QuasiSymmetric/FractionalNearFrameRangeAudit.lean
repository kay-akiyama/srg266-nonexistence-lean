/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.FractionalNearFrameAudit

/-!
# Bounded range audits for fractional near-frame columns

The exact-demand shell is complete but a single kernel reduction over every
column can retain too much state.  This module separates the mathematical
coverage theorem from bounded computations on `take`/`drop` ranges.  Concrete
modules may check ranges independently and combine them without adding local
coordinate tables or minimizing-column payloads.
-/

namespace SRG266.QuasiSymmetric

/-- The compiled start threshold bounds every column in an explicit list. -/
def CompactIndexedEmptyStartBoundOn (nearMask : ℕ) (witness : Array ℤ)
    (columns : List ℕ) : Prop :=
  ∀ columnMask ∈ columns,
    compactIndexedEmptyStartLowerBound nearMask witness ≤
      compactKernelIndexedPairWeightSum nearMask witness columnMask

/-- Executable Boolean form of a bounded column-list audit. -/
def compactIndexedEmptyStartBoundOnAudit (nearMask : ℕ)
    (witness : Array ℤ) (columns : List ℕ) : Bool :=
  columns.all fun columnMask => decide (
    compactIndexedEmptyStartLowerBound nearMask witness ≤
      compactKernelIndexedPairWeightSum nearMask witness columnMask)

/-- A kernel decision of the Boolean audit yields the corresponding semantic
range bound. -/
theorem compactIndexedEmptyStartBoundOn_of_audit (nearMask : ℕ)
    (witness : Array ℤ) (columns : List ℕ)
    (haudit : compactIndexedEmptyStartBoundOnAudit nearMask witness columns = true) :
    CompactIndexedEmptyStartBoundOn nearMask witness columns := by
  intro columnMask hcolumn
  rw [compactIndexedEmptyStartBoundOnAudit, List.all_eq_true] at haudit
  simpa [decide_eq_true_eq] using haudit columnMask hcolumn

/-- Column-list bounds compose across concatenation. -/
theorem compactIndexedEmptyStartBoundOn_append (nearMask : ℕ)
    (witness : Array ℤ) (left right : List ℕ) :
    CompactIndexedEmptyStartBoundOn nearMask witness (left ++ right) ↔
      CompactIndexedEmptyStartBoundOn nearMask witness left ∧
        CompactIndexedEmptyStartBoundOn nearMask witness right := by
  constructor
  · intro hbound
    constructor
    · intro columnMask hcolumn
      exact hbound columnMask (List.mem_append_left right hcolumn)
    · intro columnMask hcolumn
      exact hbound columnMask (List.mem_append_right left hcolumn)
  · rintro ⟨hleft, hright⟩ columnMask hcolumn
    rcases List.mem_append.mp hcolumn with hcolumn | hcolumn
    · exact hleft columnMask hcolumn
    · exact hright columnMask hcolumn

/-- Compiler rule for joining a checked prefix and suffix at any boundary. -/
theorem compactIndexedEmptyStartBoundOn_of_take_drop (nearMask : ℕ)
    (witness : Array ℤ) (columns : List ℕ) (cut : ℕ)
    (hleft : CompactIndexedEmptyStartBoundOn nearMask witness
      (columns.take cut))
    (hright : CompactIndexedEmptyStartBoundOn nearMask witness
      (columns.drop cut)) :
    CompactIndexedEmptyStartBoundOn nearMask witness columns := by
  rw [← List.take_append_drop cut columns]
  exact (compactIndexedEmptyStartBoundOn_append nearMask witness _ _).mpr
    ⟨hleft, hright⟩

/-- Reversing an enumerated range does not change its boundedness proposition. -/
theorem compactIndexedEmptyStartBoundOn_reverse (nearMask : ℕ)
    (witness : Array ℤ) (columns : List ℕ) :
    CompactIndexedEmptyStartBoundOn nearMask witness columns.reverse ↔
      CompactIndexedEmptyStartBoundOn nearMask witness columns := by
  constructor
  · intro hbound columnMask hcolumn
    exact hbound columnMask (List.mem_reverse.mpr hcolumn)
  · intro hbound columnMask hcolumn
    exact hbound columnMask (List.mem_reverse.mp hcolumn)

/-- Compiler rule for covering a shell with a forward prefix and a prefix
computed independently in reverse enumeration order.  The length equation is
the only boundary metadata carried between the two computations. -/
theorem compactIndexedEmptyStartBoundOn_of_forward_reverse
    (nearMask : ℕ) (witness : Array ℤ) (cut back : ℕ)
    (hlength : (compactNearColumnShell nearMask 0).length = cut + back)
    (hforward : CompactIndexedEmptyStartBoundOn nearMask witness
      ((compactNearColumnShell nearMask 0).take cut))
    (hreverse : CompactIndexedEmptyStartBoundOn nearMask witness
      ((compactNearColumnShellReverse nearMask 0).take back)) :
    CompactIndexedEmptyStartBoundOn nearMask witness
      (compactNearColumnShell nearMask 0) := by
  let columns := compactNearColumnShell nearMask 0
  have hreverse' : CompactIndexedEmptyStartBoundOn nearMask witness
      (columns.reverse.take back) := by
    simpa [columns, compactNearColumnShellReverse_eq_reverse] using hreverse
  have htail : columns.reverse.take back = (columns.drop cut).reverse := by
    rw [List.take_reverse, hlength]
    simp
  rw [htail] at hreverse'
  exact compactIndexedEmptyStartBoundOn_of_take_drop nearMask witness columns cut
    hforward
    ((compactIndexedEmptyStartBoundOn_reverse nearMask witness
      (columns.drop cut)).mp hreverse')

/-- Complete-shell membership transports bounded executable checks to the
semantic lower-bound premise used by the hybrid Farkas theorem. -/
theorem compactIndexedEmptyCandidateBound_of_start_bound_on_shell
    (nearMask : ℕ) (witness : Array ℤ)
    (hbound : CompactIndexedEmptyStartBoundOn nearMask witness
      (compactNearColumnShell nearMask 0)) :
    CompactIndexedEmptyCandidateBound nearMask witness := by
  intro columnMask hcolumn
  exact le_trans
    (compactIndexedEmptyCandidateLowerBound_le_start nearMask witness)
    (hbound columnMask (isCompactNearColumn_mem_shell hcolumn))

/-- The compiled start threshold bounds the columns selected by a Boolean
predicate.  The predicate partitions proof work and carries no column data. -/
def CompactIndexedEmptyStartBoundWhere (nearMask : ℕ) (witness : Array ℤ)
    (selected : ℕ → Bool) : Prop :=
  ∀ columnMask ∈ compactNearColumnShell nearMask 0,
    selected columnMask = true →
      compactIndexedEmptyStartLowerBound nearMask witness ≤
        compactKernelIndexedPairWeightSum nearMask witness columnMask

/-- Executable audit for one predicate-selected shell branch. -/
def compactIndexedEmptyStartBoundWhereAudit (nearMask : ℕ)
    (witness : Array ℤ) (selected : ℕ → Bool) : Bool :=
  (compactNearColumnShellWhere nearMask 0 selected).all fun columnMask =>
    decide (compactIndexedEmptyStartLowerBound nearMask witness ≤
      compactKernelIndexedPairWeightSum nearMask witness columnMask)

/-- A kernel decision of a predicate branch yields its semantic bound. -/
theorem compactIndexedEmptyStartBoundWhere_of_audit (nearMask : ℕ)
    (witness : Array ℤ) (selected : ℕ → Bool)
    (haudit : compactIndexedEmptyStartBoundWhereAudit nearMask witness selected =
      true) :
    CompactIndexedEmptyStartBoundWhere nearMask witness selected := by
  intro columnMask hcolumn hselected
  rw [compactIndexedEmptyStartBoundWhereAudit, List.all_eq_true] at haudit
  have hwhere : columnMask ∈
      compactNearColumnShellWhere nearMask 0 selected := by
    rw [compactNearColumnShellWhere_eq_filter]
    exact List.mem_filter.mpr ⟨hcolumn, hselected⟩
  simpa [decide_eq_true_eq] using haudit columnMask hwhere

/-- Two complementary predicate branches recover their common parent branch. -/
theorem compactIndexedEmptyStartBoundWhere_of_split (nearMask : ℕ)
    (witness : Array ℤ) (base split : ℕ → Bool)
    (hfalse : CompactIndexedEmptyStartBoundWhere nearMask witness
      (fun columnMask => base columnMask && !split columnMask))
    (htrue : CompactIndexedEmptyStartBoundWhere nearMask witness
      (fun columnMask => base columnMask && split columnMask)) :
    CompactIndexedEmptyStartBoundWhere nearMask witness base := by
  intro columnMask hcolumn hbase
  cases hsplit : split columnMask
  · exact hfalse columnMask hcolumn (by simp [hbase, hsplit])
  · exact htrue columnMask hcolumn (by simp [hbase, hsplit])

/-- The always-selected branch is the original full-shell proposition. -/
theorem compactIndexedEmptyStartBoundOn_of_where_true (nearMask : ℕ)
    (witness : Array ℤ)
    (hbound : CompactIndexedEmptyStartBoundWhere nearMask witness
      (fun _ => true)) :
    CompactIndexedEmptyStartBoundOn nearMask witness
      (compactNearColumnShell nearMask 0) := by
  intro columnMask hcolumn
  exact hbound columnMask hcolumn rfl

/-! ## Start-normalized hybrid separator -/

/-- Endpoint weights using the compiled empty-shell start lower bound directly,
and exact internal minima for the other twenty-four endpoint shells. -/
def compactIndexedStartHybridEndpointWeight (nearMask : ℕ)
    (witness : Array ℤ) (endpoint : CompactEndpointIndex nearMask) : ℤ :=
  if endpoint = compactEmptyEndpointIndex nearMask then
    -compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
      compactIndexedEmptyStartLowerBound nearMask witness
  else compactIndexedCanonicalEndpointWeight nearMask witness endpoint

/-- The indexed Farkas vector normalized directly at the compiled start. -/
def compactIndexedStartHybridFarkasVector (nearMask : ℕ)
    (witness : Array ℤ) : CompactFractionalRow nearMask → ℤ
  | .inl endpoint =>
      compactIndexedStartHybridEndpointWeight nearMask witness endpoint
  | .inr pair => compactWitnessAt witness pair.val

/-- Exact right-hand-side dot product for start normalization. -/
def compactIndexedStartHybridFarkasRhsDot (nearMask : ℕ)
    (witness : Array ℤ) : ℤ :=
  (∑ endpoint : CompactEndpointIndex nearMask,
      compactIndexedStartHybridEndpointWeight nearMask witness endpoint) +
    3 * ∑ pair : CompactPairIndex nearMask,
      compactWitnessAt witness pair.val

/-- Kernel-oriented right-hand-side dot product for start normalization. -/
def compactKernelIndexedStartHybridFarkasRhsDot (nearMask : ℕ)
    (witness : Array ℤ) : ℤ :=
  (List.ofFn fun endpoint : CompactEndpointIndex nearMask => endpoint).foldl
      (fun total endpoint => total +
        compactIndexedStartHybridEndpointWeight nearMask witness endpoint) 0 +
    3 * (List.range (compactIntersectionOnePairs nearMask).length).foldl
      (fun total pairIndex => total + compactWitnessAt witness pairIndex) 0

private theorem startHybridFoldlIntAddEqSumMap {alpha : Type*}
    (items : List alpha) (term : alpha → ℤ) (base : ℤ) :
    items.foldl (fun total item => total + term item) base =
      base + (items.map term).sum := by
  induction items generalizing base with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons]
      omega

theorem compactKernelIndexedStartHybridFarkasRhsDot_eq (nearMask : ℕ)
    (witness : Array ℤ) :
    compactKernelIndexedStartHybridFarkasRhsDot nearMask witness =
      compactIndexedStartHybridFarkasRhsDot nearMask witness := by
  rw [compactKernelIndexedStartHybridFarkasRhsDot,
    compactIndexedStartHybridFarkasRhsDot,
    startHybridFoldlIntAddEqSumMap, startHybridFoldlIntAddEqSumMap,
    zero_add, zero_add, list_sum_map_range_eq_sum_fin]
  rw [List.map_ofFn, List.sum_ofFn]
  simp

/-- A checked full-shell start bound proves every column slack for the
start-normalized empty endpoint; the other endpoints retain canonical
normalization. -/
theorem compactIndexedStartHybridEndpointWeight_nonnegativeSlack
    (nearMask : ℕ) (witness : Array ℤ)
    (hbound : CompactIndexedEmptyStartBoundOn nearMask witness
      (compactNearColumnShell nearMask 0))
    (endpoint : CompactEndpointIndex nearMask) (columnMask : ℕ)
    (hcolumn : IsCompactNearColumn nearMask
      (compactEndpointMaskAt nearMask endpoint) columnMask) :
    0 ≤ compactIndexedStartHybridEndpointWeight nearMask witness endpoint +
      compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
        compactKernelIndexedPairWeightSum nearMask witness columnMask := by
  by_cases hempty : endpoint = compactEmptyEndpointIndex nearMask
  · subst endpoint
    have hlower := hbound columnMask
      (isCompactNearColumn_mem_shell (by simpa using hcolumn))
    have hcoefficient :
        0 ≤ compactEndpointCoefficient
          (compactEndpointMaskAt nearMask
            (compactEmptyEndpointIndex nearMask)) := by
      simp [compactEndpointCoefficient]
    rw [compactIndexedStartHybridEndpointWeight, if_pos rfl]
    nlinarith [mul_le_mul_of_nonneg_left hlower hcoefficient]
  · rw [compactIndexedStartHybridEndpointWeight, if_neg hempty]
    exact compactIndexedCanonicalEndpointWeight_nonnegativeSlack nearMask witness
      endpoint columnMask (isCompactNearColumn_mem_shell hcolumn)

theorem integerDot_compactIndexedStartHybridFarkasVector_matrixColumn
    (nearMask : ℕ) (witness : Array ℤ)
    (column : CompactFractionalColumn nearMask) :
    SRG266.integerDot
        (compactIndexedStartHybridFarkasVector nearMask witness)
        (fun row => compactFractionalMatrix nearMask row column) =
      compactIndexedStartHybridEndpointWeight nearMask witness column.1 +
        compactEndpointCoefficient (compactEndpointMaskAt nearMask column.1) *
          compactIndexedPairWeightSum nearMask witness column.2.1 := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type,
    compactIndexedStartHybridFarkasVector, compactFractionalMatrix,
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

theorem integerDot_compactIndexedStartHybridFarkasVector_rhs
    (nearMask : ℕ) (witness : Array ℤ) :
    SRG266.integerDot
        (compactIndexedStartHybridFarkasVector nearMask witness)
        (compactFractionalRhs nearMask) =
      compactIndexedStartHybridFarkasRhsDot nearMask witness := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type,
    compactIndexedStartHybridFarkasVector, compactFractionalRhs,
    compactIndexedStartHybridFarkasRhsDot, mul_one]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro pair _
  ring

/-- The compiled start can normalize the empty endpoint without evaluating or
replaying the local descent. -/
theorem noCompactFractionalNearFrame_of_indexedStartHybridPairFarkas
    (nearMask : ℕ) (witness : Array ℤ)
    (hbound : CompactIndexedEmptyStartBoundOn nearMask witness
      (compactNearColumnShell nearMask 0))
    (hrhs : compactKernelIndexedStartHybridFarkasRhsDot nearMask witness < 0) :
    NoCompactFractionalNearFrame nearMask := by
  apply SRG266.no_nonnegative_rational_solution_of_integer_farkas
    (compactFractionalMatrix nearMask) (compactFractionalRhs nearMask)
    (compactIndexedStartHybridFarkasVector nearMask witness)
  constructor
  · intro column
    rw [integerDot_compactIndexedStartHybridFarkasVector_matrixColumn,
      ← compactKernelIndexedPairWeightSum_eq]
    exact compactIndexedStartHybridEndpointWeight_nonnegativeSlack
      nearMask witness hbound column.1 column.2.1 column.2.2
  · rw [integerDot_compactIndexedStartHybridFarkasVector_rhs,
      ← compactKernelIndexedStartHybridFarkasRhsDot_eq]
    exact hrhs

end SRG266.QuasiSymmetric
