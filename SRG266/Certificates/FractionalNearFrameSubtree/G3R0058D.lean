import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0058`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0058Mask : ℕ := 969051645870282

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0058Witness : Array ℤ :=
  #[113, -60, -72, -67, 38, 58, 27, 49, 13, 0, 83, -48, -8, -123, -110, 53,
  67, -32, -3, -47, 52, -63, -12, 2, -49, 5, 16, 85, 34, -57, 70, -78, -92,
  -153, 73, 81, 5, -46, -34, -42, -14, 66, -47, 0, 14, -128, -15, 32, -42,
  -72, 16, 20, 67, 47, -23, 2, -4, -76, 65, -127, -61, -10, 38, 69, 67, -13,
  -26, 29, -112, 84, 44, -2, 43, -11, 8, 69, 17, 75, -19, 48, 12, 83, -9,
  73, 43, 13, 95, 29, 35, 97, -20, 49, 110, 113, -59, 31, -1, 1, -49, 48,
  22, 0, -98, -13, -56, -31, 3, 45, 22, -62, -45, -5, -3, 12, 5, 29, -39, 4,
  -24, -34, 60, 73, 79, 2, -60, -68, -41, 22, 71, 30, -47, -119, -73, 28,
  26, 66, 43, -10, 135, 0, -79, 27, 11, 123, -51, 35, -10, 0, 32, -57, -54,
  57, 81, -38, 93, 43, 49, -40, -19, -3, 34, -83, 57, 0, -135, 33, -17, 105]

theorem fractionalNearFrameSubtreeG3R0058_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0058Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0058Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0058Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0058_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0058LowerBoundTable : List ℤ :=
  [-34, 81, 10, 3, 76, 62, 2, 34, -25, -96, -51, 273, 157, 319, 204, -149,
  61, 331, 415, -20, -154, 130, -37, 277, -17]

def fractionalNearFrameSubtreeG3R0058LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0058Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0058LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
