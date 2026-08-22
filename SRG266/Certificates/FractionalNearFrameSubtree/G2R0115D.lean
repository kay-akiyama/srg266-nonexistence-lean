import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0115`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0115Mask : ℕ := 1310220460329057

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0115Witness : Array ℤ :=
  #[34, 24, 0, -101, -146, -223, 166, 126, 162, 146, 107, 31, 70, 100, -41,
  -77, -40, -45, -27, 23, 42, 30, -43, -143, -28, -30, -64, -92, 164, 56,
  28, 112, 58, 19, -74, -202, -177, 127, 13, -31, 109, 26, 18, 110, 104, 86,
  0, -85, -196, -209, 56, 60, 157, 50, 32, -41, -60, 32, 62, 94, 71, -117,
  79, -22, 23, 47, -11, -19, -56, -22, -41, -28, 52, 38, 53, 10, 2, -21,
  -119, -46, 30, 21, -25, 28, 69, 35, 25, 112, 53, 71, 32, -25, 58, 121, 89,
  61, 1, -46, 50, -17, 95, 36, 66, 81, 48, 40, 20, 120, 54, 14, -45, 111, 8,
  91, 135, 48, 54, 142, -3, -42, -12, -54, 81, 41, -71, -134, 31, -60, 55,
  -13, -96, 61, -63, -84, 9, -47, 79, 55, 13, -132, -3, 109, -33, 46, -44,
  -68, -105, 35, 67, 14, 65, 52, 79, 7, -44, 145, -86, -34, -43, -72, 111,
  2, -1, 22, -82, -15, -24, 36]

theorem fractionalNearFrameSubtreeG2R0115_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0115Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0115Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0115Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0115_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0115LowerBoundTable : List ℤ :=
  [46, 2, 0, 123, -2, 121, 251, 260, 364, 227, 221, -109, 270, 31, 155,
  -193, 164, 358, 285, 224, 278, -21, 135, 10, 505]

def fractionalNearFrameSubtreeG2R0115LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0115Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0115LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
