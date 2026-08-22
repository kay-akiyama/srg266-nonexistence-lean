import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0527`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0527Mask : ℕ := 6780123102041105

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0527Witness : Array ℤ :=
  #[225, 238, 155, 234, 248, 296, -303, -360, -332, -410, -358, -206, 59,
  135, 175, 233, 112, 194, 49, 85, 42, 57, 96, 65, -15, 18, -26, -21, 22,
  -38, -58, -9, -211, -241, -105, -71, 67, 267, 243, 343, -258, -208, -79,
  -20, 468, -9, 33, -91, -23, 8, -27, 6, 13, -21, -67, -16, -30, -14, -17,
  -31, 31, 29, -45, 54, 29, 15, 47, -14, -26, -37, -42, 57, -16, 1, 32, -23,
  -78, 48, -1, -22, 103, 19, 17, 34, 16, 5, 10, -41, -13, -24, 51, -1, -33,
  37, -53, -98, 13, 49, -14, -46, -8, -14, -42, -20, -36, 135, 64, 86, 34,
  43, 11, 65, 26, 102, -130, -57, 59, 166, -63, 19, 20, 33, -85, -8, 77,
  -12, 51, -14, -53, 23, -20, 45, 33, 28, 55, 19, 106, -22, 3, 2, 3, 46, 0,
  39, 67, -24, -13, 27, -33, -47, 42, -12, -4, 21, -16, -31, -45, -1, -81,
  -32, 47, 24, 9, 91, -10, 0, -22, 32]

theorem fractionalNearFrameSubtreeG2R0527_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0527Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0527Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0527Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0527_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0527LowerBoundTable : List ℤ :=
  [81, 127, -61, 5, 152, 195, 373, 2, 178, 19, 210, 78, 160, -222, 266, 63,
  -8, 9, -76, -115, 73, 274, 220, 515, -256]

def fractionalNearFrameSubtreeG2R0527LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0527Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0527LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
