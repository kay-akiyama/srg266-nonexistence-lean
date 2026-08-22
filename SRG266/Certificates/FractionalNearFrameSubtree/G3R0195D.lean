import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0195`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0195Mask : ℕ := 6867816152752916

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0195Witness : Array ℤ :=
  #[0, 399, 411, 477, -1468, 2961, 1094, 105, 636, 832, 196, -773, -1041,
  -474, -1870, -1912, -1825, -1654, -150, -1316, -1812, 1042, -404, 1252,
  -32, -574, 606, -257, 1125, -188, -1310, -782, -1390, 2412, 1934, -466,
  -834, 1024, 316, -192, 1460, 1197, -1316, -1412, -234, 680, -576, -648,
  1078, -919, -287, -777, 945, 203, 80, 168, -1905, -261, 4846, 1230, -3234,
  -1175, -1961, -918, -733, -1628, -2033, 840, -1041, -346, -1748, 3165,
  -5473, 0, -1499, -1104, -119, 1102, -1026, -1202, 600, 679, 1931, -1017,
  -894, -3556, 1290, -1501, -833, -3629, 666, 836, -420, -1835, -735, 504,
  3390, -1145, 1148, 2658, 320, 3189, -1401, -842, 539, 255, 1326, 1146,
  -1505, 2771, 691, 3706, 982, 130, 3605, 305, 1023, -2861, -4330, -21,
  -216, 2288, -171, 225, 1109, 2099, 781, 412, 211, -209, 226, 179, -1758,
  -191, 375, 1659, -2524, -970, -222, 1243, -136, -2945, 520, 546, 277, 155,
  637, -501, 612, 201, 878, 189, 358, -1791, -584, -116, 484, 1298, -2977,
  -861, -2167, 1739, 1004, 571, 567, 553, -590, 861]

theorem fractionalNearFrameSubtreeG3R0195_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0195Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0195Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0195Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0195_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0195LowerBoundTable : List ℤ :=
  [-3894, 1193, 33, -935, 32, -2673, 57, 2004, -3914, 64, 1844, 3190, 7962,
  3156, 5777, 1934, -9526, -2387, -4953, -2172, -8511, 3643, 2872, -9319,
  3314]

def fractionalNearFrameSubtreeG3R0195LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0195Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0195LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
