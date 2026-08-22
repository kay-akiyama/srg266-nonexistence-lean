import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0097`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0097Mask : ℕ := 2518119481775250

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0097Witness : Array ℤ :=
  #[1, 61, -2, -79, -17, 29, 92, -65, -61, 58, -50, -9, 117, 1, -74, 86,
  -43, 34, 84, -62, 9, 28, 123, -146, 30, -63, -12, 74, -86, -63, 18, -72,
  20, 52, -30, 51, -18, 23, 63, -83, -20, 151, 15, 6, -11, 150, 61, -97,
  -107, -32, 60, -25, 35, 0, 9, 19, -13, -84, 39, -34, 34, 10, 2, -55, 57,
  42, -41, -44, 72, -44, 39, -8, 33, 57, 0, -131, -26, -8, 0, 34, -47, 91,
  40, 67, 8, 35, 86, 80, 2, -29, 18, 2, 72, -35, -112, 20, -57, -100, -14,
  -39, 5, -67, 45, -101, 19, 31, -94, 70, 144, 57, -76, -126, 27, 166, -112,
  -19, -92, -13, -43, 28, -38, -47, 83, 186, -54, 20, -98, -32, -28, -93,
  -29, 95, -48, 67, 88, 139, -9, -9, -62, 41, -5, 66, -22, -21, -67, -43,
  -57, -34, -32, -112, 41, 59, 92, 55, 102, -11, 88, -6, -74, 0, 97, 120,
  -32, -98, -4, -76, -6, 111]

theorem fractionalNearFrameSubtreeG3R0097_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0097Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0097Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0097Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0097_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0097LowerBoundTable : List ℤ :=
  [-58, 21, 83, 0, -93, 112, 1, 13, -63, 9, -17, 107, -117, 214, 364, 187,
  -3, 85, 89, -93, -218, 58, 52, 454, 210]

def fractionalNearFrameSubtreeG3R0097LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0097Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0097LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
