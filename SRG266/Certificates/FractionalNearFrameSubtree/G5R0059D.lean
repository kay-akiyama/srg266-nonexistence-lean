import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0059`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0059Mask : ℕ := 4979948446999045

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0059Witness : Array ℤ :=
  #[-1369, 207, 274, -597, -225, -228, 529, 218, 131, 1831, 107, 481, 0,
  229, 238, -861, -108, -479, -350, -625, -450, 214, -143, -956, 165, 210,
  -403, 292, 585, 70, 39, 441, 0, 762, -301, 376, -326, -365, -1183, 0,
  -900, 786, 410, 1247, 825, -50, 105, -80, -1994, 496, -79, 1386, 515, 418,
  -147, 56, 1147, 947, 493, 176, 494, -129, -233, 2015, -232, -372, -486,
  495, 234, -93, -1814, 801, -798, -73, 567, -493, -91, 314, -561, -963,
  -1106, 609, 401, 134, 307, 745, 588, 606, -591, 847, 698, 353, 73, 239,
  1259, 122, -211, -299, -295, -101, 478, 165, -342, -329, 37, -1, -828,
  -477, -101, -41, 124, -21, 143, -291, 327, -60, 1124, -698, -35, -271,
  331, 22, 67, 241, -1501, -699, 963, -1259, -592, 862, 1497, -1212, 180,
  -206, 157, 239, 1017, 3, -617, -129, -384, 1249, -59, -164, -281, -1795,
  -1724, -217, 231, 664, -72, 204, 349, 665, -282, 918, -346, 762, -224,
  1091, -757, -725, -861, -135, 533, 276, 837, -631]

theorem fractionalNearFrameSubtreeG5R0059_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0059Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0059Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0059Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0059_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0059LowerBoundTable : List ℤ :=
  [-330, -14, 756, -271, 293, 32, 401, 480, -488, 254, 3318, -1588, -346,
  564, 3120, 2098, 590, 1024, -55, -1037, 3193, 3421, -2733, 1314, 465]

def fractionalNearFrameSubtreeG5R0059LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0059Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0059LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
