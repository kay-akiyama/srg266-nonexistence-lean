import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0151`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0151Mask : ℕ := 1376362169319826

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0151Witness : Array ℤ :=
  #[99, 13, 33, -125, 125, -10, 11, 103, 149, -82, 15, 30, -28, 17, 64, -44,
  57, -106, 2, -120, -104, 33, -67, 15, 75, 126, 16, 151, 87, 65, 100, 60,
  32, 83, -59, 37, -60, 60, -51, -129, 14, -76, 44, -124, -116, 139, -30,
  142, 151, 28, -29, -28, 12, -192, 118, 83, 19, 61, -185, 93, -136, -63,
  -24, 42, 129, -7, -21, -10, 86, 18, 88, 149, -90, 42, 29, -71, -30, 67,
  -84, 5, 111, 88, -18, 141, -7, 38, 0, 0, 102, -104, -165, 8, -43, -28, -3,
  -80, 39, 29, -15, -56, -42, -46, -101, 87, -16, 48, 36, 136, 229, -85, 73,
  114, 183, -97, 31, 108, -139, 85, -105, -67, 154, -38, 0, 110, 124, 104,
  114, -101, 20, 34, 71, -17, -1, -93, 32, 19, -6, -68, 9, -64, -42, -172,
  94, -15, 149, 43, 45, 87, 51, -25, 7, 71, 69, -72, 29, 60, 180, -22, 89,
  110, 94, -83, 15, -36, -69, 60, 187, 6]

theorem fractionalNearFrameSubtreeG2R0151_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0151Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0151Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0151Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0151_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0151LowerBoundTable : List ℤ :=
  [110, 263, 154, 2, -85, -75, 325, 177, 422, 951, 832, 29, 482, 67, 153,
  234, -41, 102, -115, 63, 466, 11, 537, 497, 155]

def fractionalNearFrameSubtreeG2R0151LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0151Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0151LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
