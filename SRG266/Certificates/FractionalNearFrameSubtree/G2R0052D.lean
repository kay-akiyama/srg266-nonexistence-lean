import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0052`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0052Mask : ℕ := 936555774153354

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0052Witness : Array ℤ :=
  #[70, -35, 82, 132, 107, -1, -73, -50, -87, -183, -237, 37, 25, 99, -26,
  -51, -69, -134, -111, 14, 30, 120, 184, 93, 45, 20, -53, 131, -126, -112,
  -19, -37, 61, 84, -39, -20, 49, 119, -7, -182, 40, 88, -48, 149, 10, -53,
  -24, 16, 88, 144, -61, -6, -155, 51, -121, 65, -23, -16, -41, 110, -10,
  -93, -36, 101, 179, -237, 55, -8, 72, -79, 26, -73, 46, 61, -53, -34, -18,
  -86, 20, 123, -26, -186, -67, -118, -62, 132, -29, 36, 94, 90, 16, -46,
  -203, 14, -72, -74, -81, 13, 183, -100, -96, 56, -13, -4, -23, 43, -9,
  -96, -78, 135, 31, 80, 61, -171, -50, 34, -16, 31, 61, 111, -79, 95, 22,
  -11, -40, 20, 6, 66, 67, -36, -8, 85, 88, 4, -144, -9, 81, 47, -21, 39,
  -19, 69, 136, -145, -193, 123, 17, 167, 8, 41, 181, 0, 109, 4, 86, 11, 82,
  42, 44, 54, -63, 81, 106, 53, 52, 71, 137, -120]

theorem fractionalNearFrameSubtreeG2R0052_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0052Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0052Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0052Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0052_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0052LowerBoundTable : List ℤ :=
  [-65, 324, 2, -147, 164, 94, 2, 172, -28, 457, 83, 401, 184, -84, 152,
  -33, 122, 260, -29, 10, -208, 388, -92, -270, 400]

def fractionalNearFrameSubtreeG2R0052LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0052Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0052LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
