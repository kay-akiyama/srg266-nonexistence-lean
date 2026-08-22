import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0070`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0070Mask : ℕ := 866324533914121

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0070Witness : Array ℤ :=
  #[-13, -35, 94, -82, 0, 0, 54, 4, 99, 68, 156, 61, -146, -90, -36, -18,
  -75, 0, 54, 36, 47, -68, 95, -39, 145, 37, 43, 47, -4, -40, -9, 91, -24,
  66, -78, -19, -7, 1, -24, 11, -64, 27, 38, 99, 191, -90, -111, -13, 92,
  -12, 93, -18, 61, 44, 14, -30, 67, -101, 0, 41, 0, 36, 21, 26, 58, -41,
  -28, 15, 49, -37, -14, -40, 61, 15, -1, -48, -6, 54, 8, 187, 53, -8, 84,
  102, 48, 15, 52, 63, 118, 36, 78, 90, 95, 12, 9, -83, 24, 107, 90, -3, 8,
  -45, -4, 35, 40, -68, 75, -51, 13, 16, 95, -121, 37, -13, -31, 32, 52,
  -12, 56, 29, 4, -54, -5, -111, -2, -18, -11, -28, -38, 69, -182, -17, 67,
  3, -20, 0, -16, 7, -20, -39, 125, 93, 34, -13, -30, 11, -31, 17, -2, -33,
  -87, 153, -98, 141, 13, 83, 136, 37, 15, -70, 80, 85, 38, 127, 177, -37,
  49, -146]

theorem fractionalNearFrameSubtreeG1R0070_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0070Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0070Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0070Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0070_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0070LowerBoundTable : List ℤ :=
  [174, 168, 282, 80, 220, 267, 2, 109, 269, 147, 142, 34, 197, 231, 53,
  368, 359, 137, 181, 131, 412, 430, 262, 264, 30]

def fractionalNearFrameSubtreeG1R0070LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0070Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0070LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
