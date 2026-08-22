import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0475`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0475Mask : ℕ := 5809437813159064

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0475Witness : Array ℤ :=
  #[15, 29, -54, 66, -8, -21, 35, 19, -17, -21, -32, 8, 13, 7, 28, 17, -21,
  5, 22, -11, 41, -9, -23, 7, 13, -3, -57, -21, -14, 0, -19, -6, 35, 9, -17,
  39, -33, -9, 28, -10, -8, -33, 43, 11, 25, -14, 53, -9, -54, 14, -12, -38,
  48, 3, -5, -69, -20, 24, 6, -43, 36, 28, 50, -8, -7, 34, -7, -59, 0, 27,
  32, -39, 45, 25, -1, 39, 31, -8, -6, -36, -9, -23, -12, 52, 26, -15, -8,
  30, 3, 11, -54, -51, 0, 8, -13, -65, 1, 65, 20, -10, 7, -20, -58, 45, 42,
  -45, -21, -8, -55, 27, 19, 89, -13, 81, 59, -57, 27, 26, 22, 10, -42, -91,
  4, 55, -21, -6, 29, 25, -65, -21, 15, -26, 18, 11, -68, 108, -15, -41, 28,
  5, 63, -26, 22, -9, 10, 36, -5, 31, 18, 59, -27, -20, 9, 74, 35, -7, 57,
  2, -8, -36, 0, 69, -12, -36, 6, 4, 7, 53]

theorem fractionalNearFrameSubtreeG2R0475_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0475Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0475Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0475Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0475_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0475LowerBoundTable : List ℤ :=
  [-12, 70, 53, 61, 2, 8, 23, -13, 97, 222, 21, 202, 156, 134, -155, 6, 312,
  64, 66, 10, -68, -57, 16, 11, 11]

def fractionalNearFrameSubtreeG2R0475LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0475Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0475LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
