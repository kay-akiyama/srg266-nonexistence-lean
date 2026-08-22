import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0221`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0221Mask : ℕ := 2479018099709074

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0221Witness : Array ℤ :=
  #[-121, 317, 316, 141, -77, 765, -31, -285, 686, 85, 1022, 38, 33, -65,
  -292, -477, 29, -333, -71, 219, -634, 62, 160, -448, 540, 476, 302, -210,
  4, 113, 271, -935, -235, 156, 564, 58, -477, 102, 345, 744, 65, 85, 373,
  186, 131, -22, -439, 12, -511, 109, 0, -724, 194, 628, 129, 750, 33, 576,
  -264, -115, -511, 733, -269, 314, 44, 718, -232, 181, -537, -61, 34, -210,
  105, -488, -674, 185, 62, -338, -33, -372, -352, -220, 306, 624, 524,
  -367, 576, 873, 91, -116, 152, 406, 506, -464, -37, -405, -111, -307,
  -618, 245, -405, -691, -176, 396, 622, 258, 1309, -398, -2, 346, 340,
  -195, -673, -96, 58, 330, 830, -25, -210, -111, 0, -117, -505, -375, 449,
  96, 425, 486, 669, 235, 84, 725, -130, 195, -402, 42, 295, 79, 179, 425,
  216, -348, -246, -129, 524, -183, -426, -174, -556, 258, -207, -352, -33,
  -389, -326, 249, 726, 619, -20, 124, 268, 462, 5, 405, -114, -435, -760,
  -257]

theorem fractionalNearFrameSubtreeG2R0221_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0221Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0221Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0221Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0221_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0221LowerBoundTable : List ℤ :=
  [124, 561, 275, 387, -514, 922, 32, 753, 498, 500, 522, 2150, 990, 100,
  2114, 2048, 556, -869, 1274, 2011, -634, -918, 1844, -516, 4093]

def fractionalNearFrameSubtreeG2R0221LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0221Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0221LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
