import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0129`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0129Mask : ℕ := 1353131365204554

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0129Witness : Array ℤ :=
  #[35, 73, 69, 54, 138, 90, -173, -116, -102, 41, -179, 17, 32, 66, 86, 47,
  49, 103, 42, 7, 0, 30, 7, -81, -61, -57, 0, -31, -34, -74, 21, -16, -49,
  55, 24, 0, -6, 33, 17, 104, -11, 41, -16, 75, -57, 17, -40, 34, 61, -26,
  99, 47, 23, 64, 1, -98, 1, -36, 63, 9, 18, 29, -6, -40, 1, 3, 1, 108, 8,
  -10, 70, 18, 49, 36, 31, 21, 51, 44, -12, 123, 11, -24, 4, 54, 81, -21,
  -23, 27, -45, -55, 28, -20, -44, -128, 26, 18, 68, -26, 9, 9, 38, 13, -1,
  41, 18, -67, -40, 11, 21, 6, 3, 46, -4, -40, -23, 55, -43, -14, -5, -103,
  73, -73, 9, -12, 64, 87, -60, -36, -21, -96, -21, 63, 16, 83, -81, 50, 26,
  44, -23, -76, 71, -35, -9, 33, -64, -29, -6, -8, 90, 59, 38, -7, 35, -19,
  2, 88, 59, 14, 70, 27, -61, 58, 120, 85, 38, 89, -12, -21]

theorem fractionalNearFrameSubtreeG2R0129_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0129Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0129Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0129Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0129_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0129LowerBoundTable : List ℤ :=
  [49, 133, 201, -38, 2, -8, 195, 80, 238, -40, 209, 211, 10, -236, 374, 32,
  227, 12, 301, 217, 340, 360, 361, 175, 10]

def fractionalNearFrameSubtreeG2R0129LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0129Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0129LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
