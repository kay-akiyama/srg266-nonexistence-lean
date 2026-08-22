import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0002`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0002Mask : ℕ := 261464325494929

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0002Witness : Array ℤ :=
  #[-1803, -2002, -1952, -1602, -2467, -2252, 771, 490, 1826, 1522, 158,
  772, 1054, 1241, 1988, 1767, 0, 582, 558, 504, -474, -531, 599, -28, -51,
  -416, 397, 12, -341, 240, 361, -187, 19, 299, 33, -892, -23, 947, 1323,
  150, -174, -877, -753, 126, -644, 1496, 480, 179, 2543, -531, -889, 793,
  1204, -919, -1514, -112, -768, -4, 51, 1742, 181, 299, -552, 178, -46,
  825, -49, 1043, 864, -510, 152, 1308, 276, 534, -1031, 485, -575, 53,
  -515, 60, 566, -250, -110, -772, -1014, 325, -646, 678, -70, -68, -134,
  774, -606, 457, 540, 65, 27, -301, 463, 321, 45, 475, -521, -398, 19, 236,
  98, -765, -871, -1535, -1773, -942, -305, -2084, -1345, 2416, 2712, -898,
  259, 491, -61, 859, 765, 758, -850, -953, 983, 54, 777, -190, 1036, -648,
  -719, 345, -1284, -1115, -292, -344, 279, 154, 44, 101, 938, 280, 625,
  226, 662, 239, 313, 421, 222, 236, 735, 305, 619, -211, 249, 316, -343,
  162, -461, -1317, -152, -501, -1481, 425, 425, 154]

theorem fractionalNearFrameSubtreeG3R0002_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0002Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0002Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0002Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0002_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0002LowerBoundTable : List ℤ :=
  [-601, -175, -560, 626, 1438, -1024, 68, 240, 2308, 3904, 101, -468, -783,
  1777, -3782, 99, 99, 1922, 100, -1104, 2313, 99, 2805, 161, 4392]

def fractionalNearFrameSubtreeG3R0002LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0002Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0002LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
