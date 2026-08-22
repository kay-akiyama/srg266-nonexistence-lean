import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0264`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0264Mask : ℕ := 5369570178830924

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0264Witness : Array ℤ :=
  #[-4, 10, 51, 2, -34, 113, 8, 117, 75, 27, 90, -25, -83, -72, -30, -56,
  -17, -27, 43, 29, -26, -2, -70, -3, -18, 16, 48, 9, 87, 61, 43, 75, -32,
  -66, 103, 108, -17, -78, -14, 90, 68, 161, -101, 23, 27, 15, 31, 18, 89,
  -23, -15, 30, 67, 154, 65, 27, 117, 105, -9, 37, 27, -84, 62, 102, -56,
  -92, -38, -89, 27, -73, 27, 16, -68, 46, 55, -4, 85, 47, -19, -55, -22,
  -28, -17, -30, -26, 10, 43, 65, -42, -25, 20, -11, 39, 45, 27, -26, 10,
  -48, 87, 95, 29, 4, 58, 47, 51, 41, 59, 94, -2, 17, -2, 13, 72, 119, -26,
  -16, -69, -68, -57, -15, -58, 25, 143, 67, 21, 36, -64, -94, -73, -15, 47,
  16, -78, 79, -137, 117, -8, 46, -84, 15, 41, 50, -4, -64, 70, 20, -35, 50,
  -38, 36, 22, 24, 21, 45, 7, 14, -1, 15, 38, -10, 103, 60, 72, 47, -163,
  -32, -96, 16]

theorem fractionalNearFrameSubtreeG2R0264_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0264Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0264Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0264Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0264_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0264LowerBoundTable : List ℤ :=
  [115, 74, 241, 122, 165, 167, 82, 69, 274, 10, 188, -20, 229, 335, 112,
  209, 487, 145, 137, 9, 381, 120, 214, 200, 1]

def fractionalNearFrameSubtreeG2R0264LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0264Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0264LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
