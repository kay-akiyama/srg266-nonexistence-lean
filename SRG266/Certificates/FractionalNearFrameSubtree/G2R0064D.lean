import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0064`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0064Mask : ℕ := 954129842930002

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0064Witness : Array ℤ :=
  #[313, 27, 51, 0, -122, -14, 74, 71, -104, 10, 22, 183, 82, -1, 252, -45,
  65, 446, 87, -49, 103, 314, 340, 25, 191, 120, -53, -190, -100, -271, -40,
  98, -184, -24, 66, -259, -41, 51, 139, 190, 63, -74, 66, 283, 31, 452, 80,
  481, -173, 167, -154, -236, -189, -180, -259, 191, 56, -126, 0, -77, 270,
  49, -43, -67, 24, -118, -118, 166, -28, 138, -80, 132, -363, 59, -175, 21,
  -134, 250, 0, 200, 139, 79, 83, -353, -25, 182, -48, 117, 83, 119, 84, 88,
  146, 156, 67, -333, 58, 49, 99, 228, 54, -124, 195, 45, 136, -175, -242,
  107, 178, 107, 147, -525, -266, -242, 155, 237, 94, -79, 204, -84, 243,
  65, -265, -201, 49, 69, 88, 223, 89, 172, -39, -85, -112, -154, -1, 184,
  -304, 215, -50, 133, 161, 87, 22, -13, 77, 72, 54, 141, 125, 251, -63,
  204, -28, -162, 214, 220, 32, -95, -55, 110, -256, 277, -68, 94, -88, -66,
  22, 30]

theorem fractionalNearFrameSubtreeG2R0064_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0064Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0064Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0064Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0064_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0064LowerBoundTable : List ℤ :=
  [210, 330, 41, 101, 693, 523, 553, 433, 116, 410, 293, 673, -192, 353,
  663, 156, 310, 193, 11, 442, -73, 890, 618, 814, 549]

def fractionalNearFrameSubtreeG2R0064LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0064Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0064LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
