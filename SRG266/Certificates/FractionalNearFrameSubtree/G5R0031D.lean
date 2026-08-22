import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0031`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0031Mask : ℕ := 1367290326786121

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0031Witness : Array ℤ :=
  #[58, 31, 55, 62, 52, 28, 59, -5, 121, 41, 14, 0, -93, -132, -222, -91,
  57, 27, -26, 65, -8, 13, 36, 31, -44, 98, 26, 4, -47, 4, 36, 80, 6, 38,
  80, -17, 47, -1, 88, -8, -57, -22, -189, -57, -9, 35, -27, 31, 102, -7,
  -41, 115, -109, -26, 57, 71, -101, -12, -53, -13, 66, 86, -19, -28, -64,
  -71, -5, -6, 2, 61, 10, 0, -162, 37, -36, -10, 8, -30, 26, -44, -19, -8,
  8, 45, -94, -65, -42, 50, 29, 12, 45, 64, -36, 23, -8, 25, -5, -22, -144,
  36, 49, 53, 11, 20, 12, 21, 72, -20, -21, -90, -86, -29, 33, 2, 54, -220,
  -18, 39, -12, -33, 54, 19, 114, -153, -79, 33, 66, -72, 53, -5, -6, 9, 71,
  12, 170, -157, 15, -61, -13, -98, -121, -94, 114, 12, 119, 57, -99, 74,
  -52, 70, 182, 61, 14, 0, -46, -37, 0, 11, 61, -20, 25, 40, -59, 86, 74,
  134, -28, 11]

theorem fractionalNearFrameSubtreeG5R0031_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0031Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0031Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0031Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0031_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0031LowerBoundTable : List ℤ :=
  [-60, 67, 1, 1, 113, 1, 44, 26, -86, 317, -370, -81, 183, 45, 30, -139,
  -290, 200, 269, 140, 11, 209, -16, 263, 204]

def fractionalNearFrameSubtreeG5R0031LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0031Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0031LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
