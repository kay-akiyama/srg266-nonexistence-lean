import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0035`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0035Mask : ℕ := 529856745841030

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0035Witness : Array ℤ :=
  #[-170, 630, 2388, 1498, 2526, 1211, -1637, -673, 748, 0, 115, 1185,
  -2063, -2159, -950, -213, -633, 181, -542, -420, -366, 368, -374, -837,
  -282, 1068, -810, 99, 1719, 1118, 1259, 2325, -106, -214, 93, -881, 259,
  -596, 986, 1216, -188, -704, -682, -869, 682, 754, 829, 713, -28, 375,
  556, -62, 25, -801, 338, -464, -219, -411, -758, 290, 685, -1174, 817, 12,
  -119, -489, 610, -681, 510, 925, 191, 1017, 801, 109, 44, 478, 92, -544,
  651, -177, 304, -407, -58, -89, -33, 227, 59, 668, -240, 375, -12, 806,
  351, -197, -605, 57, 378, -30, 312, -277, -67, 192, 1301, -410, 497, 254,
  -65, 306, 256, -43, 47, -739, 386, -717, 383, 245, 401, -164, 233, -341,
  -718, -450, -1003, -662, 437, 898, 207, 242, -183, -480, -576, 763, 498,
  265, -5, 182, -734, 395, 33, 45, 423, 613, 532, 609, 721, 594, 311, 563,
  664, -104, 987, 565, 401, 75, 374, -461, -653, -428, 383, -91, -1665, 123,
  148, -853, -80, -377, -453, -407]

theorem fractionalNearFrameSubtreeG1R0035_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0035Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0035Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0035Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0035_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0035LowerBoundTable : List ℤ :=
  [919, 32, -919, 4276, 1085, -118, 413, 2285, -507, 2341, 938, -310, 2235,
  1233, -450, 101, 99, 102, 4864, 7720, 3205, 1298, 2500, 1134, -619]

def fractionalNearFrameSubtreeG1R0035LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0035Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0035LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
