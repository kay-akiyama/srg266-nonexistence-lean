import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0040`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0040Mask : ℕ := 954165781695762

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0040Witness : Array ℤ :=
  #[195, -364, 212, -585, -114, 263, 264, 213, 55, 458, 395, -274, -100,
  -751, 36, 3, -109, -103, 381, 330, -307, 246, 498, 4, 409, 236, 29, 237,
  -38, -183, 196, -436, 366, -376, 1290, -159, -493, -209, -524, 90, 331,
  -335, -37, -746, -214, 213, -782, -171, 532, -322, 337, 280, -184, 538,
  19, -109, 304, 725, 253, -1490, 417, 39, 279, 485, -941, -855, 627, 716,
  -32, -593, 848, -747, -951, 329, 609, -738, -686, -218, 1190, 900, 261,
  267, 3, 436, 1054, 380, 232, 355, -499, -86, 212, -101, 230, -217, 710,
  414, 87, -330, -276, 72, -164, 57, -40, 396, -71, -64, 89, 135, -46, -339,
  -116, -214, -532, 0, 336, -75, 274, 730, -203, 217, 84, 578, -985, -1480,
  -212, 58, 113, -27, -121, 2, 0, -1032, 412, 445, -466, 727, 351, 8, 281,
  391, 610, 251, -394, 351, 58, -102, -432, 475, -55, 190, 794, 615, 93,
  -455, 151, 0, 133, -290, 363, 210, -443, -385, -75, -330, 102, -4, 231,
  914]

theorem fractionalNearFrameSubtreeG3R0040_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0040Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0040Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0040Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0040_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0040LowerBoundTable : List ℤ :=
  [-89, 485, 718, 2100, 1260, 25, -149, -337, 31, 1430, 1499, -1575, -16,
  1228, -326, 234, -1335, 1393, 1803, 1145, 3366, 28, 1345, 99, -752]

def fractionalNearFrameSubtreeG3R0040LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0040Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0040LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
