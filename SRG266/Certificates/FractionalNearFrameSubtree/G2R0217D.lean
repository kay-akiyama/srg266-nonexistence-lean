import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0217`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0217Mask : ℕ := 2378620134216721

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0217Witness : Array ℤ :=
  #[45, 134, 441, 104, 87, 186, -18, -446, -566, 0, -997, 765, -896, -1206,
  734, 685, -548, 1405, 832, 415, 378, 117, -593, -419, 462, 351, -152, 297,
  496, 42, -869, 1824, 636, 922, 525, 1049, -1615, 0, -809, 92, -371, -1103,
  1043, -219, 2259, 629, -409, -370, -22, -539, -741, 1312, 875, 403, 9,
  -840, -380, 417, 562, 249, -330, -441, -423, 342, 1178, 712, 427, -1088,
  -532, -59, 51, -991, -1496, 1402, 404, 93, -325, -364, 467, 921, -1634,
  -139, -191, 383, 421, 423, -571, -42, 293, -776, -363, 1315, 68, -1154,
  1364, -719, -1058, -179, 296, 404, -682, 1283, 4, 299, -140, 774, 771,
  429, 729, 204, 415, -926, 1905, 219, -2003, 930, 1251, 938, 529, 768,
  -534, -854, 412, 249, 87, 703, 514, 235, -340, 330, 313, 489, -1508, -487,
  610, 835, 615, -193, -778, -602, 452, -607, -146, 862, 847, -63, -273,
  692, 150, 1213, 864, 56, 191, 625, 1155, -1623, -852, -928, -361, -2048,
  44, 571, -1028, 172, 310, 974, 1614, -2749]

theorem fractionalNearFrameSubtreeG2R0217_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0217Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0217Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0217Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0217_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0217LowerBoundTable : List ℤ :=
  [116, 1457, 893, -24, 32, 2110, 957, 319, 469, 1337, 100, 882, 2882, 1515,
  3122, 982, 3312, 126, 2033, 762, 2855, -899, 99, 2786, -365]

def fractionalNearFrameSubtreeG2R0217LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0217Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0217LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
