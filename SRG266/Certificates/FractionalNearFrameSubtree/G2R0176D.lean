import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0176`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0176Mask : ℕ := 1384875062935768

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0176Witness : Array ℤ :=
  #[142, -26, 19, 25, -13, 71, 22, 34, -8, -44, -12, 30, -31, -91, 90, -48,
  1, -53, -73, 46, 32, 0, -15, -17, 53, 0, 31, 59, -20, 149, -104, 27, 98,
  -6, -65, -48, -27, -64, 53, -121, -174, -20, 72, -53, -67, 43, -137, 50,
  117, 93, 1, -60, 89, 59, 18, -3, 29, 60, -33, -40, -54, 23, -25, -35, -60,
  34, 0, 2, 78, 12, 28, -18, 4, -6, -58, 99, -108, -42, 14, 64, 29, -17, 67,
  53, 31, 15, 26, 138, 33, 53, 63, 4, -4, 24, -54, 23, -8, 35, -73, 14, 22,
  22, 43, 49, 15, 50, 57, 43, -65, -78, -35, -51, -74, -94, -13, 12, 26,
  -92, -87, -49, -62, 25, -9, 3, -48, -45, 15, -4, 7, 20, -43, -2, -79, -22,
  -10, 80, 53, -16, 179, 8, -40, -71, 83, 49, -94, 102, 81, -83, -28, 16, 1,
  26, 34, 14, -7, -1, -22, -62, 11, 36, -76, 3, -10, -36, -38, 2, 44, 63]

theorem fractionalNearFrameSubtreeG2R0176_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0176Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0176Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0176Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0176_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0176LowerBoundTable : List ℤ :=
  [-63, -47, 34, 46, 2, -13, 92, 61, 2, 1, -68, -144, -65, 220, -17, 203,
  -393, 326, 17, 5, 43, -100, 208, 239, 284]

def fractionalNearFrameSubtreeG2R0176LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0176Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0176LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
