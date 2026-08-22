import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0050`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0050Mask : ℕ := 963571093181586

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0050Witness : Array ℤ :=
  #[7, 15, 55, -5, -65, -47, -94, 76, -40, -135, -27, 22, 110, -160, 140,
  68, 63, 79, 106, 48, -69, 11, -38, -13, 92, -81, -36, -23, -153, -221,
  102, -84, -53, -41, 14, 59, 158, -205, -76, -105, 177, 69, 232, 70, 9,
  -29, 68, -105, -113, -15, 102, 32, 89, -270, 126, 147, -91, 0, -23, -151,
  -114, 112, 31, 25, -111, -35, 58, 41, -45, -115, 27, -21, 48, 10, 11, -37,
  0, -32, 5, -6, 47, -68, -25, 22, -231, -25, 68, -13, 19, 105, 10, 174, 18,
  -44, 64, -44, 0, -14, 75, -26, 113, -172, -89, 63, -14, 115, -3, -113,
  -38, 30, -130, 47, 147, -103, -119, -106, 78, 17, -74, 38, 162, 204, 35,
  -24, 35, 40, 34, 43, -75, 93, 50, -177, -16, -43, 118, 35, -75, -52, -29,
  67, 0, -77, 16, 145, -231, 81, -70, 133, 108, 49, 234, -11, 82, 21, -76,
  -201, 38, 22, 105, -178, -48, 105, -86, 186, 56, -59, -128, 98]

theorem fractionalNearFrameSubtreeG3R0050_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0050Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0050Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0050Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0050_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0050LowerBoundTable : List ℤ :=
  [-151, 1, -59, 2, -81, 53, -155, -69, 23, 559, -37, 431, -169, 193, -124,
  755, 215, -128, -178, 418, -414, 10, 434, 10, 48]

def fractionalNearFrameSubtreeG3R0050LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0050Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0050LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
