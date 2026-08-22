import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0070`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0070Mask : ℕ := 5261837669753105

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0070Witness : Array ℤ :=
  #[29, -13, 6, -76, -32, -11, 42, 123, -37, 62, 61, -64, -31, -24, -41,
  -118, 93, -38, 13, 88, -22, -2, -30, -110, -40, -55, 47, 77, 31, 45, -82,
  -73, -46, 79, 26, 91, 42, 40, -49, -45, -73, 20, 71, 0, -6, -32, 62, 32,
  29, 88, 15, 68, 15, 35, -99, -3, -28, 31, 0, 15, 75, 17, -10, 28, 6, 60,
  11, -50, 58, 39, 4, 9, -5, -36, -38, -3, -24, -8, 52, 15, -8, 23, 17, -7,
  41, 38, -27, -50, -59, -84, -39, -78, -46, 25, 98, 42, 45, -69, -11, 10,
  27, 7, 34, -28, -24, 59, -47, -34, -82, 67, 13, -67, -103, -74, -56, -7,
  56, 7, 52, 26, 30, -15, -22, 71, -32, -2, -80, 21, -68, 25, 26, 36, 36,
  57, -11, -25, -48, 2, -33, -22, 23, 19, 47, 2, 21, 43, 14, 6, -23, -34,
  27, 0, -47, -40, -70, 61, -10, 16, 8, -1, -63, -58, 49, 51, 39, 31, 68,
  -7]

theorem fractionalNearFrameSubtreeG5R0070_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0070Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0070Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0070Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0070_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0070LowerBoundTable : List ℤ :=
  [-40, 6, -60, 43, -78, 75, -59, 0, 83, 89, -14, -10, -123, 125, 30, 35,
  102, 10, 209, 11, 111, 10, 129, 175, 25]

def fractionalNearFrameSubtreeG5R0070LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0070Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0070LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
