import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0483`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0483Mask : ℕ := 5810603026518818

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0483Witness : Array ℤ :=
  #[81, -90, 32, 39, 72, 47, -66, 27, 49, -60, 83, 4, -48, 27, 96, -53, 116,
  -128, 3, 11, 28, 1, 35, 124, 25, -30, 27, 0, 17, -31, 88, 81, 97, 42, 38,
  -162, -87, -156, 56, 41, 12, 5, -49, -132, -41, -76, -137, -30, 71, 110,
  72, 70, -27, -83, 122, 78, 52, 23, 13, -9, -19, -54, 22, -51, 58, 31, 109,
  50, -10, 26, 0, -19, -7, 69, 50, -62, 108, 30, -70, 3, 12, -22, 2, -35,
  -56, 36, 64, 42, -14, 10, 80, -32, -12, 63, -43, -71, -26, 41, -73, -41,
  40, 46, 43, 4, -39, 44, 15, -14, 76, 27, -15, -5, -45, 18, 36, 38, 109, 7,
  50, -21, 22, -47, -44, 64, 142, -79, -101, -74, 62, -113, 41, 64, -16,
  -22, -99, 107, 38, 59, 51, -28, 35, -15, 67, 71, 11, 18, 126, 76, 58, -21,
  32, -17, -8, -67, 72, 8, 64, -55, 30, 23, -93, 65, 24, -25, 58, -44, 25,
  42]

theorem fractionalNearFrameSubtreeG2R0483_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0483Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0483Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0483Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0483_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0483LowerBoundTable : List ℤ :=
  [50, 144, 154, 212, -61, 72, 58, 198, 93, 339, 157, 170, 90, 9, 214, 252,
  443, -118, 10, 508, 246, -16, -33, 9, 305]

def fractionalNearFrameSubtreeG2R0483LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0483Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0483LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
