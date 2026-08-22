import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0042`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0042Mask : ℕ := 956354153775330

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0042Witness : Array ℤ :=
  #[-147, 1033, -1008, -557, -247, 1270, 0, 1039, 2779, 2059, 2827, -2796,
  -1784, -1596, -838, -552, 136, -211, -795, -1866, -180, -671, 961, -336,
  -1225, 341, 948, 1420, 3105, 804, 2512, 90, 0, -109, 875, -3227, -3085,
  1660, 402, -1009, -2098, -2384, 2414, 2479, 2118, 720, -520, 1122, 591,
  2435, -2052, -1413, 1371, 1768, 872, -999, -1094, 792, 853, -88, 153,
  -833, -514, 139, -289, 1007, -1665, -121, 48, 763, 2384, 959, 804, 270,
  1575, 514, 1017, 1772, -51, 817, -295, -845, -700, 630, 603, 802, 550,
  1707, 1405, 910, -706, -999, -285, 1818, -366, 21, 1356, -300, 207, -17,
  733, -610, -112, -118, 468, -704, 559, 350, -559, 0, -879, 12, 344, 867,
  78, -188, 1579, 983, 428, 550, -2103, 1379, 486, -818, 888, 537, 434,
  1556, 1147, 989, -1665, -265, 175, 393, 1096, 222, 151, 268, -741, -29,
  -25, -810, 336, -1104, -110, 78, -290, 218, -1092, -443, -772, 290, -46,
  -203, 1305, 519, 194, 39, 701, 427, -73, -315, 145, -592, 668, -110, -844,
  1171]

theorem fractionalNearFrameSubtreeG3R0042_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0042Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0042Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0042Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0042_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0042LowerBoundTable : List ℤ :=
  [1345, 1006, 3928, 2387, 2664, -370, 2157, 106, 1341, -1589, 1073, 2396,
  1714, 1909, 6109, 2596, 9695, -243, 8223, -208, 3240, 9275, 5025, 443,
  100]

def fractionalNearFrameSubtreeG3R0042LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0042Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0042LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
