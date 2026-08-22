import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0057`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0057Mask : ℕ := 964875551083112

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0057Witness : Array ℤ :=
  #[70, -84, 42, -37, 107, 28, -106, -60, -124, -29, 31, -44, 83, 72, 9, -9,
  -12, 42, 5, 57, -55, 33, 51, -20, -70, -41, 16, -57, 55, 66, -12, 75, 11,
  30, 83, -138, -134, 18, -182, -6, -51, 0, 53, -11, -87, 24, 85, 50, 0,
  -81, 128, -18, 32, 36, -86, 49, 10, -80, 101, 84, 9, 7, -48, -108, 27,
  132, -77, -106, -26, 20, -50, -44, 17, 61, 41, 1, 1, -56, 105, 29, 17, 68,
  -2, 13, 0, -9, 29, -30, -11, 28, 5, 20, 2, -37, 48, 86, -49, -102, -125,
  -24, -33, -110, 39, 48, 29, 91, -87, -68, 14, -133, -36, -30, -65, 24,
  -88, 24, 52, 89, 91, -43, -12, -22, -27, -9, -20, 72, -74, 40, -7, -16,
  -37, 112, -25, 53, 0, 146, 107, 0, 95, 29, 50, -15, -57, 14, 53, -65, 4,
  22, -18, 27, 31, 63, -104, 28, -8, -73, 109, -77, -52, -63, 4, -23, 92,
  -35, 19, 115, 73, 0]

theorem fractionalNearFrameSubtreeG3R0057_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0057Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0057Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0057Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0057_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0057LowerBoundTable : List ℤ :=
  [-83, 103, 3, 3, 2, 2, 68, -169, -30, -51, 345, 9, 71, 206, 384, -276, 20,
  8, 248, 60, 48, -182, 25, 174, 9]

def fractionalNearFrameSubtreeG3R0057LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0057Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0057LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
