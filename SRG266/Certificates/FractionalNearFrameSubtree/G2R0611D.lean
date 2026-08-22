import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0611`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0611Mask : ℕ := 9578853732829705

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0611Witness : Array ℤ :=
  #[0, 52, 46, 32, 16, 31, 0, 8, 20, 4, -49, 0, -90, 37, -81, -101, -85, 85,
  -37, -82, -49, -52, -54, -14, -49, -44, -54, -60, 80, 112, 9, 48, -14, 13,
  56, 14, -56, -9, 0, -22, -29, 0, 13, 103, 13, -44, -2, 22, 14, 29, -14,
  -108, 5, -61, 0, -37, 50, 115, 1, 1, 2, -4, -6, 10, -2, -103, -12, 50, 41,
  27, 1, -97, 0, -76, -69, 12, 52, -137, -9, 18, 16, -8, -93, -10, -18, -36,
  158, 16, -90, 11, -68, -11, 25, 39, 93, 112, -128, -22, -18, -1, -12, -42,
  37, 34, 36, -30, 117, 25, 83, -8, 14, -5, 49, -31, -16, -1, 8, -8, -6,
  -32, -54, -60, -17, -158, 118, 34, 17, 18, 55, 6, -40, -195, -26, -1, 35,
  -4, -122, 157, -37, 33, -51, -129, 76, 53, 46, 97, 39, 23, -128, 25, 45,
  15, -69, 81, 6, -22, 93, -125, 61, 172, 6, 12, 75, -8, -69, -14, 134,
  -244]

theorem fractionalNearFrameSubtreeG2R0611_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0611Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0611Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0611Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0611_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0611LowerBoundTable : List ℤ :=
  [-83, -46, 2, 48, 3, -18, -74, -115, -117, 256, -198, -255, 134, 405, -62,
  153, -196, 71, -31, -58, -21, 10, -128, 28, 9]

def fractionalNearFrameSubtreeG2R0611LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0611Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0611LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
