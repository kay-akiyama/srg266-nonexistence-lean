import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0103`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0103Mask : ℕ := 954133976231188

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0103Witness : Array ℤ :=
  #[154, -80, -87, 190, -119, 58, 107, 28, 65, -8, 84, -34, 60, -125, 117,
  33, 106, -17, 17, 82, 22, -1, -210, -167, 41, 18, 82, 110, 160, 58, -41,
  140, -103, -99, 29, 54, 208, -15, -38, -272, -11, -79, -85, 108, -5, 168,
  141, 202, -9, -35, 70, 60, 223, 14, -23, -98, -70, -1, -6, -43, -30, -80,
  125, -44, 62, -8, -48, 81, -51, 30, 23, 27, -33, 231, -21, -33, 118, 182,
  40, 16, 140, 95, -108, 27, 1, 154, -18, -12, 68, -147, 90, -62, -225, 131,
  89, 186, -78, 93, -17, 93, -73, 94, 28, -139, -175, 23, -12, -16, 105,
  137, -109, 1, 0, 46, -152, -114, -8, 85, 100, 57, 85, -109, -31, 35, 30,
  64, -79, -2, -99, 15, -8, 77, -19, 33, 136, -72, 92, 118, -50, 19, 76, 6,
  95, -83, -20, 92, 39, 147, 22, 122, 18, -44, -53, -111, 106, -56, 32, 32,
  19, -26, -190, -73, -122, -58, -1, -64, 83, 212]

theorem fractionalNearFrameSubtreeG1R0103_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0103Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0103Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0103Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0103_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0103LowerBoundTable : List ℤ :=
  [110, 51, 2, 274, 245, 136, 73, 329, 107, 139, 10, 258, -225, -344, 90,
  112, 110, 580, 253, 529, 558, 48, 624, 521, 565]

def fractionalNearFrameSubtreeG1R0103LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0103Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0103LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
