import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0144`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0144Mask : ℕ := 1362068501807522

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0144Witness : Array ℤ :=
  #[1358, 1199, 922, 887, 3005, 620, 982, -61, -833, 43, 74, -1564, -1036,
  -1950, -1481, -297, 18, -433, -1666, -1714, -772, 629, -186, -487, -422,
  -1524, 2461, 1777, 1267, 2695, 70, 670, 839, 684, 2019, 11, -440, 695,
  878, 79, -1497, 115, 0, 146, -1116, -726, -506, 2549, 2099, 2299, -1724,
  -129, -1250, 159, 2134, 1866, -1272, -1336, 505, 899, -755, 521, 24, -269,
  733, 685, 299, -350, -117, 51, 1642, 543, 798, 538, 141, 1760, -535, 2281,
  455, -1270, 1926, -174, 1033, -1376, -1614, -1034, 1500, -753, 61, -873,
  892, -878, -247, -210, -81, -480, 1937, -893, 0, 617, -287, -257, -1510,
  -252, -640, 287, 533, -1373, -273, 296, 649, 1676, -176, -532, 0, 355,
  2307, -1144, -1088, 250, -1016, -1227, -444, 311, -819, -506, 3077, -1262,
  15, -60, -883, 730, 185, 3, -2623, 1190, 684, 876, 519, 582, -764, 150,
  825, 179, 958, -434, 1218, 149, -941, -462, 66, -944, -1113, -93, 1110,
  45, 231, -80, 169, 698, -32, 780, -600, -569, -491, 690, 2510, -549]

theorem fractionalNearFrameSubtreeG2R0144_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0144Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0144Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0144Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0144_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0144LowerBoundTable : List ℤ :=
  [-271, -54, -11, -2778, 32, 345, 5, 5042, 2888, 654, 101, 8651, 538, 100,
  1767, 2591, -706, 2785, 4459, -1592, 2265, 2960, 13037, 326, 7876]

def fractionalNearFrameSubtreeG2R0144LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0144Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0144LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
