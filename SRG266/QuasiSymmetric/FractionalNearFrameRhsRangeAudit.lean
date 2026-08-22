/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.FractionalNearFrameRangeAudit

/-!
# Bounded endpoint-sum audits for fractional near-frame separators

The start-normalized right-hand side contains twenty-five independently
reconstructed endpoint weights.  Reducing their total in one declaration
retains every shell minimum at once.  This module exposes a proof-producing
boundary: concrete modules may check exact sums on bounded endpoint lists,
join those equalities, and then discharge the original right-hand-side
inequality.

Endpoint indices and partial sums are theorem conclusions, not trusted
certificate fields.  A wrong split or value fails ordinary kernel checking.
-/

namespace SRG266.QuasiSymmetric

/-- The universal endpoint-index list in the order used by the kernel RHS. -/
def compactIndexedStartHybridEndpointIndices (nearMask : ℕ) :
    List (CompactEndpointIndex nearMask) :=
  List.ofFn fun endpoint => endpoint

/-- Exact value of the start-normalized endpoint weights on an explicit index
list. -/
def CompactIndexedStartHybridEndpointSumOn (nearMask : ℕ)
    (witness : Array ℤ) (endpoints : List (CompactEndpointIndex nearMask))
    (value : ℤ) : Prop :=
  (endpoints.map fun endpoint =>
    compactIndexedStartHybridEndpointWeight nearMask witness endpoint).sum = value

/-- Executable Boolean form of a bounded endpoint-sum equality. -/
def compactIndexedStartHybridEndpointSumOnAudit (nearMask : ℕ)
    (witness : Array ℤ) (endpoints : List (CompactEndpointIndex nearMask))
    (value : ℤ) : Bool :=
  decide ((endpoints.map fun endpoint =>
    compactIndexedStartHybridEndpointWeight nearMask witness endpoint).sum = value)

/-- A kernel decision of the Boolean equality yields its semantic form. -/
theorem compactIndexedStartHybridEndpointSumOn_of_audit (nearMask : ℕ)
    (witness : Array ℤ) (endpoints : List (CompactEndpointIndex nearMask))
    (value : ℤ)
    (haudit : compactIndexedStartHybridEndpointSumOnAudit nearMask witness
      endpoints value = true) :
    CompactIndexedStartHybridEndpointSumOn nearMask witness endpoints value := by
  unfold CompactIndexedStartHybridEndpointSumOn
  exact of_decide_eq_true haudit

/-- Exact endpoint sums compose across concatenation. -/
theorem compactIndexedStartHybridEndpointSumOn_append (nearMask : ℕ)
    (witness : Array ℤ)
    (left right : List (CompactEndpointIndex nearMask))
    (leftValue rightValue : ℤ)
    (hleft : CompactIndexedStartHybridEndpointSumOn nearMask witness left
      leftValue)
    (hright : CompactIndexedStartHybridEndpointSumOn nearMask witness right
      rightValue) :
    CompactIndexedStartHybridEndpointSumOn nearMask witness (left ++ right)
      (leftValue + rightValue) := by
  unfold CompactIndexedStartHybridEndpointSumOn at hleft hright ⊢
  rw [List.map_append, List.sum_append, hleft, hright]

/-- Compiler rule for joining a checked prefix and suffix at any boundary. -/
theorem compactIndexedStartHybridEndpointSumOn_of_take_drop (nearMask : ℕ)
    (witness : Array ℤ) (endpoints : List (CompactEndpointIndex nearMask))
    (cut : ℕ) (leftValue rightValue : ℤ)
    (hleft : CompactIndexedStartHybridEndpointSumOn nearMask witness
      (endpoints.take cut) leftValue)
    (hright : CompactIndexedStartHybridEndpointSumOn nearMask witness
      (endpoints.drop cut) rightValue) :
    CompactIndexedStartHybridEndpointSumOn nearMask witness endpoints
      (leftValue + rightValue) := by
  rw [← List.take_append_drop cut endpoints]
  exact compactIndexedStartHybridEndpointSumOn_append nearMask witness
    _ _ _ _ hleft hright

private theorem foldlAddEqSumMap {alpha : Type*}
    (items : List alpha) (term : alpha → ℤ) (base : ℤ) :
    items.foldl (fun total item => total + term item) base =
      base + (items.map term).sum := by
  induction items generalizing base with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- A checked total endpoint sum reduces the start-normalized RHS inequality
to the inexpensive indexed pair total and integer arithmetic. -/
theorem compactKernelIndexedStartHybridFarkasRhsDot_lt_of_endpoint_sum
    (nearMask : ℕ) (witness : Array ℤ) (endpointSum : ℤ)
    (hendpoints : CompactIndexedStartHybridEndpointSumOn nearMask witness
      (compactIndexedStartHybridEndpointIndices nearMask) endpointSum)
    (hnegative : endpointSum +
      3 * (List.range (compactIntersectionOnePairs nearMask).length).foldl
        (fun total pairIndex => total + compactWitnessAt witness pairIndex) 0 < 0) :
    compactKernelIndexedStartHybridFarkasRhsDot nearMask witness < 0 := by
  unfold CompactIndexedStartHybridEndpointSumOn at hendpoints
  rw [compactKernelIndexedStartHybridFarkasRhsDot, foldlAddEqSumMap, zero_add]
  change
    ((compactIndexedStartHybridEndpointIndices nearMask).map fun endpoint =>
        compactIndexedStartHybridEndpointWeight nearMask witness endpoint).sum +
      3 * (List.range (compactIntersectionOnePairs nearMask).length).foldl
        (fun total pairIndex => total + compactWitnessAt witness pairIndex) 0 < 0
  rw [hendpoints]
  exact hnegative

end SRG266.QuasiSymmetric
