import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0090`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0090Mask : ℕ := 2508661560644754

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0090Witness : Array ℤ :=
  #[386, 585, 761, -1552, -292, -42, 854, -143, 0, -773, 538, 245, 571,
  -415, -1766, -92, 2, 1157, 510, -1908, -158, 177, -197, -1341, -1230,
  -1572, -161, 668, 1021, 1496, -212, -45, -261, 1084, -169, 62, 346, 385,
  -961, -294, -244, 786, -141, 1729, 194, 481, 269, 646, -267, -770, -556,
  -383, 145, -862, 564, -1117, 216, -537, 513, 464, 241, -231, 741, -993,
  874, 1667, -595, 22, -1796, -1078, 139, 318, -901, -901, -296, -558,
  -1539, 1149, 1006, -590, 1575, 1285, 2374, 694, 940, 568, -1463, 357, -94,
  -593, 69, 647, -330, -289, 303, 1462, 1595, -472, -513, 608, 58, 238,
  -166, 1561, 1386, -277, -883, -250, 392, -1075, 30, 206, 667, 1352, -273,
  -1871, 15, 97, -666, -553, -252, -123, 298, -473, 36, 702, 529, 1108, 730,
  -120, -824, 1112, -670, 1093, 566, 1126, 440, 2313, 650, 1388, 1038, 473,
  186, 0, -1133, 1305, 798, 1689, 375, 935, 85, 405, -828, 722, -1096, -933,
  -276, -58, -711, 200, -2060, -161, 1443, 497, -45, 326, -52, 1455]

theorem fractionalNearFrameSubtreeG3R0090_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0090Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0090Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0090Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0090_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0090LowerBoundTable : List ℤ :=
  [210, 2428, 1235, 33, -153, 2490, 33, 2586, 123, 5624, 763, 5042, 848,
  5871, -580, 3110, 101, -412, 3164, -495, 549, 2411, -1971, 4977, 581]

def fractionalNearFrameSubtreeG3R0090LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0090Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0090LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
