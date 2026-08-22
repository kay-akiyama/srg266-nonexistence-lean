import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0014`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0014Mask : ℕ := 266869690261765

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0014Witness : Array ℤ :=
  #[111, 50, 160, 205, 255, 156, -78, -125, -6, -34, 7, -94, -101, -228,
  -163, -72, -122, -182, -138, -168, -148, -120, -132, 152, 15, 7, 7, -26,
  65, 183, 208, 147, -168, -135, -66, -188, 72, 216, 120, 134, -75, -109,
  68, -126, 115, -33, 38, -95, 42, -67, 114, 68, 32, -27, 8, 41, -67, -16,
  -46, 70, 116, 22, -41, 106, 23, -9, -29, -28, -79, 55, -11, 15, 66, 87,
  -25, 42, 51, -128, 104, -144, 81, -62, 19, -38, -143, 149, 98, -78, 26,
  60, 9, 14, -31, -20, -9, -50, -111, -117, 123, -27, 109, 63, -13, -18,
  -76, -18, 47, 79, 61, 22, 53, 7, -53, 2, -3, -160, -71, 32, 28, -4, -62,
  -32, 52, 127, -108, -86, 30, 65, 83, -13, 20, -8, 143, 5, 116, 21, 87,
  -73, 9, 0, 107, -56, 102, 36, 14, 37, 81, -43, -3, 78, -117, -40, 93, 11,
  54, -71, -27, -27, -62, -75, 66, 6, 58, 83, -31, 121, -30, 64]

theorem fractionalNearFrameSubtreeG1R0014_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0014Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0014Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0014Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0014_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0014LowerBoundTable : List ℤ :=
  [-64, 80, -61, 1, -24, -37, 78, -64, 42, 266, 245, 332, 10, 58, 107, 92,
  107, 396, 205, -9, -167, 8, 448, 457, -123]

def fractionalNearFrameSubtreeG1R0014LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0014Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0014LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
