import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0555`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0555Mask : ℕ := 6841800133874260

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0555Witness : Array ℤ :=
  #[-462, 490, 986, -350, 1467, -1473, -1331, -36, -1015, -818, -331, 656,
  320, 65, 1342, 283, 94, 535, 151, -839, -947, -156, -406, 267, -300, 143,
  -215, 247, -171, -68, -865, -1448, -1357, 991, 678, 1284, 366, -45, -151,
  1350, -369, 630, -703, -1718, 370, 114, -352, -410, 454, 711, -62, 602,
  -300, -713, -32, -531, 762, 485, 848, 8, -557, 12, -727, -293, -145,
  -1167, -1854, -15, 1365, 172, 251, 125, -153, -169, 402, 549, 209, -684,
  505, 891, 424, 184, -1160, 941, 1368, 1112, 1249, 69, -141, -757, 944,
  701, 1601, 63, 669, 1442, 720, -168, -797, -844, -248, -606, -1621, 152,
  -1048, 358, 489, 413, -3, -770, 467, 956, 443, -21, -410, 518, -360, -972,
  -720, 793, 935, 711, 1093, -774, 410, 367, -437, -538, -515, 32, 264,
  1433, -378, 664, 285, -101, -479, 393, 368, 289, 218, 355, 599, 177, 966,
  235, 747, 598, -275, -35, 1371, -238, -83, -1269, -399, -403, 1305, 540,
  -262, -195, 931, 573, 988, 42, -1206, 669, -1321, 498]

theorem fractionalNearFrameSubtreeG2R0555_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0555Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0555Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0555Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0555_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0555LowerBoundTable : List ℤ :=
  [-33, 1582, 33, 1601, 1418, 32, -1214, 32, 953, 7315, 1140, 1979, 1122,
  4574, 100, 1339, 1502, 1404, -733, 3156, 1505, -230, 100, -207, 1343]

def fractionalNearFrameSubtreeG2R0555LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0555Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0555LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
