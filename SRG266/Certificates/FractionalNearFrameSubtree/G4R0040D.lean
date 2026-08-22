import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0040`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0040Mask : ℕ := 5471567696348434

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0040Witness : Array ℤ :=
  #[-59, 158, -134, -104, -146, -149, 638, 156, -20, 617, 211, -399, -153,
  -389, -136, -341, -258, 386, 93, -105, -17, -32, 247, -235, -105, 126,
  167, 398, 0, 8, -19, 127, -5, -177, -331, 77, 67, -62, 24, 10, 296, 141,
  267, 320, 298, -107, -236, 197, -341, -496, -130, 171, -53, -455, 1, -89,
  -16, -42, -89, 47, -369, -57, 348, -30, -160, -192, -201, -95, -317, -87,
  167, 55, -78, 240, 125, -178, 387, 171, 243, 59, -17, -197, -26, -18,
  -115, -147, -391, 198, 149, 122, 43, -6, 150, -199, 324, 2, 169, 155, -34,
  192, -118, 145, 321, 283, -199, -165, 37, 214, -1, 371, 420, 347, -333,
  -656, -306, 109, 97, 39, 75, -287, 2, 253, 98, 174, -137, 145, -77, -149,
  -188, 212, 243, -75, 44, 139, -64, 56, 558, 464, -40, 16, 234, -257, 81,
  -287, 356, -183, 40, 171, 27, 15, -38, -57, -29, -301, 268, -300, 87, 156,
  152, 60, 59, 196, -96, -63, 16, 182, 26, 43]

theorem fractionalNearFrameSubtreeG4R0040_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0040Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0040Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0040Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0040_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0040LowerBoundTable : List ℤ :=
  [-52, 451, 387, -216, 1, 443, 493, -183, 13, 882, 948, 256, 434, -15, 931,
  140, 883, -339, -251, -872, 586, -241, 594, 744, 9]

def fractionalNearFrameSubtreeG4R0040LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0040Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0040LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
