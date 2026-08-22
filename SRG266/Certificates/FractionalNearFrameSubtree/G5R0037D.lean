import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0037`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0037Mask : ℕ := 1604369299513441

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0037Witness : Array ℤ :=
  #[62, -15, 30, -14, 51, 8, 31, 40, 35, -14, 34, 13, -80, -66, -51, -32,
  -30, -24, -6, -20, 21, 8, -16, -18, 73, -15, -13, -50, 5, 45, 33, 34, -22,
  54, -48, 17, 40, -2, -31, 6, -35, -60, 47, -7, -50, 67, -2, -32, 29, 70,
  -19, -24, -12, -82, -56, -29, -71, 68, -55, -12, 162, 10, -3, -4, 0, -11,
  42, 17, -22, 14, -37, 11, 23, 31, 3, -49, 36, 2, 4, 29, 139, 20, 0, -20,
  16, 14, -16, -65, -24, 54, -123, -33, -22, -1, -46, -60, 39, 61, -39, 34,
  80, -79, -17, 5, -27, 43, -83, -40, -58, -24, 58, 13, 11, -5, 1, 63, -23,
  12, -22, 91, -27, -36, -127, 24, -28, -70, 136, -27, -14, -35, -97, 38,
  -38, -45, 62, -42, 48, 9, -80, -19, 0, -5, 93, -123, 7, 71, 22, 26, -37,
  29, -11, -12, -33, -49, 0, -4, 13, 54, -30, 16, 78, 44, 135, 3, 42, -21,
  -53, 16]

theorem fractionalNearFrameSubtreeG5R0037_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0037Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0037Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0037Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0037_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0037LowerBoundTable : List ℤ :=
  [-71, 0, 3, -69, 73, -141, 63, -13, 2, -54, 213, -21, -305, -28, 135, -1,
  86, 73, 10, 189, -80, 10, -188, 119, 211]

def fractionalNearFrameSubtreeG5R0037LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0037Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0037LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
