import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0027`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0027Mask : ℕ := 953957505213190

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0027Witness : Array ℤ :=
  #[-1262, -1961, 1646, -163, 1547, -255, 2287, 7903, -729, -5988, -1162,
  2736, 0, 235, 0, 3898, 10345, 7115, 9425, 3549, 1441, 2881, -3757, 3255,
  -6140, -9654, -4702, 72, -4814, -2987, 1268, 537, 7153, 754, 3557, -2106,
  -5143, 2487, 6115, 8312, -7441, -6755, -3615, -485, 981, 0, 604, 3559,
  3158, 2101, -1451, -7205, 2187, 550, -3612, 1033, 154, -2438, 6515, 6553,
  7502, -2988, -4639, -8216, -4337, -3448, 1333, 1411, 21, -4609, -4216,
  2846, 5153, -929, 4882, 4929, 812, 3287, 2310, -9677, 2928, 625, 1653,
  2523, 4233, -1079, -1863, -11439, -3471, 1157, 1091, 2245, -4727, 3363,
  5090, 809, -132, 4692, -4723, -2010, 1098, -593, -3251, 6465, -3334, -632,
  2778, -2600, 4369, 3197, -4555, -3757, -3881, 6354, 394, 3396, -605, -31,
  -1706, 2764, 6377, 1350, -5342, 947, -2992, 4782, 10154, 1382, 1427,
  -4384, 6575, 4746, 1164, 6771, -2023, -6441, 5651, 453, -4941, 6537, 2643,
  699, 4170, 271, 7669, 5025, 8207, 9263, 1056, 1446, 4909, 5167, 1004,
  -3305, 9893, 2205, 1396, -3398, 6817, 7647, -9688, 4730, 1168, -4119,
  1011, 3604, -5301, 1269]

theorem fractionalNearFrameSubtreeG3R0027_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0027Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0027Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0027Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0027_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0027LowerBoundTable : List ℤ :=
  [3238, 18813, 4188, 13340, 9903, 4818, 5038, -1732, 14536, 1945, 8930,
  23141, 23745, 22448, 6447, -21787, 23394, 20996, 10597, 2231, 18433,
  17464, 1631, -2762, 13277]

def fractionalNearFrameSubtreeG3R0027LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0027Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0027LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
