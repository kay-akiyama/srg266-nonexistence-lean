import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0124`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0124Mask : ℕ := 5861261652658578

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0124Witness : Array ℤ :=
  #[-577, -3575, 2066, -1495, -1449, -383, -1858, -496, 190, 0, 2299, 3117,
  1583, -2902, 2534, -452, -2336, -984, 641, 900, 891, 710, 1230, 566, 690,
  -1957, -2014, 0, -1836, 16, -1129, 818, -2649, 2341, 1048, 2734, 0, 1014,
  4672, 1474, 1140, 1000, 753, -894, -854, 186, -1825, 136, 340, 94, 878,
  -1753, 3409, 3466, 2351, 1787, -411, -330, -480, 1472, -21, -46, 788,
  1654, 1585, 14, -1191, -1417, 371, 960, 663, -475, 2072, -1157, -99, 1276,
  -992, -46, -1259, 1218, 2071, -3649, 616, 185, 1133, 1173, 2405, -1041,
  893, -1181, -781, 1124, 226, 1539, 333, 1031, 2628, -118, 1281, 3547,
  -2588, -115, 1044, 133, 2291, 682, 2501, 758, -818, -563, 1857, -2613,
  -356, 1533, 653, 2444, -451, 2295, 1917, -3486, 1920, 874, 739, -463,
  -1296, 2048, 163, 1726, -227, -498, -1705, -41, -188, -3688, 2001, 772,
  2898, -165, 295, 601, -452, 3067, -1591, 2764, 289, 977, 0, 663, -3295,
  186, -1480, 1677, -2218, 737, 974, 1333, 690, 1485, -1550, -667, 2112,
  3548, 541, -307, 3145, 2242, -237, 806]

theorem fractionalNearFrameSubtreeG5R0124_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0124Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0124Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0124Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0124_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0124LowerBoundTable : List ℤ :=
  [1941, 3819, 5876, 2809, 5993, 2524, 5094, 2964, 1969, 11333, 3830, 8643,
  2796, 5253, 7503, 11136, 11879, 10329, 9355, -4504, 2526, 7433, -285,
  -3500, 4490]

def fractionalNearFrameSubtreeG5R0124LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0124Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0124LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
