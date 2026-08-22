import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0293`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0293Mask : ℕ := 5386216921613074

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0293Witness : Array ℤ :=
  #[-60, -76, -11, 8, 67, 55, 59, 112, 101, 115, 82, -163, -43, -130, -22,
  -200, 35, 58, -23, 84, 28, -99, -78, 17, 31, 26, -71, -29, 205, 90, -19,
  -64, 4, -103, -94, 85, 45, 47, 18, -4, -26, -57, 151, 7, 15, -52, 1, -15,
  -65, -49, 11, -25, 55, 67, 41, 98, -28, 3, 57, -25, 30, 36, -76, -87, 52,
  59, -60, -126, 49, 53, 25, 26, -36, 16, 45, 87, 21, 29, 42, -40, 16, -3,
  42, 46, 80, 69, -35, -2, -61, -71, 134, 77, -34, -87, 56, 46, 11, -51, 35,
  -98, 54, 43, 42, 18, -124, -55, -63, -21, -18, -42, -41, -56, 109, 151,
  -54, -45, 12, -32, -12, -5, 43, -13, -101, -83, -64, 26, 8, -10, -95, 48,
  -79, 5, 13, -44, 63, 55, -16, -71, -18, -34, 106, -66, -5, 12, -48, 104,
  -45, -16, -16, -44, 115, 23, -9, -235, 84, 11, -18, 0, -92, 7, -236, 39,
  37, 34, 41, -62, -271, 19]

theorem fractionalNearFrameSubtreeG2R0293_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0293Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0293Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0293Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0293_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0293LowerBoundTable : List ℤ :=
  [-102, -141, -108, 117, -103, -1, -52, 1, -62, 59, -194, -224, 21, -280,
  205, 86, 87, 104, 263, 98, 181, -160, 64, -115, -62]

def fractionalNearFrameSubtreeG2R0293LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0293Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0293LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
