import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0187`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0187Mask : ℕ := 1388186452869488

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0187Witness : Array ℤ :=
  #[55, -63, 0, 33, -24, 15, 26, 57, -8, 39, -68, 70, -64, -45, 22, -100,
  -33, -107, 76, -3, -3, 26, 9, 29, 26, -55, 70, -9, 58, 6, 45, 96, 1, -11,
  -35, -92, -52, -116, -56, -11, 9, -37, -94, -134, -91, 52, 28, 55, 39,
  104, 10, -5, 2, 3, 53, 76, 0, -52, 67, 61, 4, -14, -37, -48, -49, 76, 18,
  48, -79, 25, 49, -96, 55, 37, -48, 64, -2, 25, 28, 6, 86, 139, -12, 65,
  119, -59, 74, -38, -72, -38, 23, 47, 59, -19, -45, -94, -49, -85, -25,
  -35, 52, 14, -73, -47, -57, -10, -23, 14, 21, -30, -139, -72, 0, 73, 57,
  49, 64, 11, 61, 12, -87, -26, -11, 9, 22, 14, -63, 15, -1, -28, -6, 113,
  81, -31, -15, -22, 37, 92, 10, -21, -27, -45, -5, -22, 73, 45, -30, -5,
  16, 10, 135, -21, -40, -24, -71, -4, 66, 27, -29, 79, 44, -19, -69, 67,
  59, -43, 36, 38]

theorem fractionalNearFrameSubtreeG2R0187_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0187Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0187Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0187Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0187_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0187LowerBoundTable : List ℤ :=
  [-61, 131, 55, -62, 52, 21, 1, 2, 2, 9, 234, -35, 8, 243, 5, 59, 9, 9,
  -126, 210, 190, -87, 8, -19, 139]

def fractionalNearFrameSubtreeG2R0187LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0187Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0187LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
