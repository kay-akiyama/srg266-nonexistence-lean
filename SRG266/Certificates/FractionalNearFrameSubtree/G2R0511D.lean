import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0511`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0511Mask : ℕ := 5812261038768724

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0511Witness : Array ℤ :=
  #[-30, -47, 41, -135, 70, 46, 79, 109, -56, 94, 7, -58, -73, -45, 40, 37,
  -23, 43, -37, 46, 110, -65, 18, -25, 28, 27, -14, 44, -121, 28, -25, -83,
  -132, 3, 139, 119, -3, 0, 28, 19, 78, 118, -99, -36, 59, 40, -22, 68, 3,
  -31, 39, 81, -59, 5, -5, -91, 24, 31, -73, 47, 51, 76, 136, -51, -66, 36,
  20, -12, -34, -43, 28, -60, 42, 88, 181, -28, -160, 65, 109, 70, 136, -35,
  -79, 52, 111, 10, 183, 54, 31, 146, 108, 36, 40, 48, 63, -31, 78, -4, -51,
  -35, -74, 168, 56, 4, -42, -34, 29, -145, -71, -76, 71, 123, 72, 72, -12,
  -73, -7, -60, -20, 138, -16, 40, 7, -52, 5, 34, -74, -144, 6, 61, 78, 47,
  53, -29, -24, 38, 77, 35, -4, 33, -64, -60, 43, -56, -85, 25, 60, 10, 59,
  -85, 115, -91, 75, -38, 47, -22, 23, 42, 47, -13, 128, 24, 38, -125, 14,
  -76, 18, -31]

theorem fractionalNearFrameSubtreeG2R0511_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0511Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0511Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0511Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0511_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0511LowerBoundTable : List ℤ :=
  [103, -11, 48, 260, 205, 204, 178, 266, -113, 171, 174, 10, 9, 130, -78,
  -9, 8, 698, 340, 174, 276, 166, 29, 449, 259]

def fractionalNearFrameSubtreeG2R0511LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0511Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0511LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
