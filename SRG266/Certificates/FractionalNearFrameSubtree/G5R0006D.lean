import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0006`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0006Mask : ℕ := 798024882159683

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0006Witness : Array ℤ :=
  #[-65, 30, -180, 91, -57, -4, -23, -84, 41, -11, 57, 63, 51, 2, -60, 0,
  -69, -39, -45, -78, -46, -27, 84, 80, 58, 82, 105, -48, -53, -41, 3, 24,
  -45, -1, -17, -74, -18, -35, 84, 23, 0, 16, 3, 99, 36, 25, 29, -40, -35,
  16, 34, 65, 26, 19, -8, -12, 131, 17, 88, -15, -29, 85, -33, -2, 26, -146,
  -151, -1, 51, 2, -57, -11, 20, -16, 4, 128, 121, 25, 124, 56, 54, 71, 113,
  22, 29, -108, -42, -11, 65, -15, -8, 31, -23, 4, 59, 67, 55, -17, -46, 28,
  -27, -38, -20, 46, -134, -55, -108, -53, -18, -13, 61, 72, 13, 154, -65,
  -157, -48, -16, 0, 9, -18, 64, -1, -13, -19, 17, 15, -21, -28, 140, -59,
  -8, -65, 31, 87, 17, 85, 21, -36, -1, -45, 1, -46, -66, 47, -110, 44, 136,
  7, -23, -120, -13, 8, -93, 45, 0, 27, -92, 62, 45, -33, -64, -29, 99, 211,
  54, 67, 19]

theorem fractionalNearFrameSubtreeG5R0006_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0006Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0006Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0006Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0006_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0006LowerBoundTable : List ℤ :=
  [-21, 54, 66, 82, 2, 88, -51, 2, 87, 66, -232, 189, 230, 224, -42, 255,
  10, 76, 180, 315, 218, -350, 94, 109, 130]

def fractionalNearFrameSubtreeG5R0006LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0006Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0006LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
