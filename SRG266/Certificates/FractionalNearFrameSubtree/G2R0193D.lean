import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0193`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0193Mask : ℕ := 1870926032372322

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0193Witness : Array ℤ :=
  #[-31, -41, 13, 83, 0, -94, -187, 0, -24, -3, 0, 45, 9, 60, 14, 12, -26,
  13, 18, 52, 55, -96, 102, 30, 51, 113, -30, 48, -50, -57, -30, 30, 11,
  -27, -58, 63, 85, -94, -94, 66, 3, 150, -111, -114, -152, 44, 32, -32, -1,
  23, 69, -48, -67, -90, -130, 0, 46, 185, 0, -1, -96, 1, 7, 62, 35, -14,
  -101, -23, 37, 8, 90, 16, -18, 5, 44, 16, 39, 111, 8, 55, -27, 105, -88,
  -14, -37, 88, -134, 14, 5, -21, 163, -77, 47, 8, -7, 166, 18, 71, 75, 91,
  18, -34, 106, 61, -13, -156, -208, -145, -47, 27, -65, 66, 120, 173, 56,
  30, 28, 54, 12, -31, 21, -120, -137, 36, -9, -34, 18, -82, -43, 17, 23,
  -19, 165, 4, -19, -22, 43, -46, 16, 1, -3, 52, 14, 78, 63, -71, -50, -94,
  7, 39, 81, 30, -2, -17, 22, 33, 3, 27, 75, 93, -76, -39, 11, 55, -43, -4,
  13, 43]

theorem fractionalNearFrameSubtreeG2R0193_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0193Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0193Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0193Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0193_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0193LowerBoundTable : List ℤ :=
  [-53, 30, 1, 178, 171, 3, 80, 3, -179, 87, 169, 167, -189, 252, -107,
  -114, -112, 558, 291, 152, 11, 396, 132, 98, 36]

def fractionalNearFrameSubtreeG2R0193LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0193Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0193LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
