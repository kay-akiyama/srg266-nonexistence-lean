import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0456`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0456Mask : ℕ := 5794883259519640

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0456Witness : Array ℤ :=
  #[87, 160, -15, 30, -12, 165, 215, -134, 219, -173, -1, 133, -194, 68, 38,
  52, 242, -31, 60, 72, 28, -357, 167, -6, 198, -37, 162, -184, 26, -9, 31,
  -44, 49, 88, 219, 89, 130, -33, -91, 12, 75, 53, 197, 53, -79, -144, 57,
  -58, 101, -75, -230, 403, 37, -6, 126, 20, 170, -33, -122, 32, -139, 214,
  -44, 202, 1, 93, 49, 249, 61, -149, 3, -112, -186, -74, 150, 147, -147,
  140, 31, 197, 233, 10, -3, -22, 161, -108, 296, 74, 135, -93, -131, 28,
  47, -116, -132, -10, -84, -61, 28, -102, 292, 45, 76, 130, 84, -91, 44,
  -119, -116, -67, 84, -246, 143, 65, -70, 178, 6, -38, -253, -425, 237,
  111, 91, 39, 302, 78, 190, 180, -59, -75, -91, -153, -29, -44, -130, 292,
  184, 139, -245, -210, 5, 108, 185, 145, 268, -123, 153, 77, 124, 4, 273,
  130, -3, 137, 91, 52, 145, 23, -21, -71, -101, -28, -113, 205, 39, 418,
  71, 131]

theorem fractionalNearFrameSubtreeG2R0456_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0456Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0456Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0456Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0456_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0456LowerBoundTable : List ℤ :=
  [311, 443, 445, 337, 529, 76, 104, 462, 502, 286, 8, 447, 753, 968, 24,
  433, 1007, 319, 304, 448, 9, 408, 1000, 663, 572]

def fractionalNearFrameSubtreeG2R0456LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0456Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0456LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
