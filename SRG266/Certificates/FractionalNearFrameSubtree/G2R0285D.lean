import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0285`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0285Mask : ℕ := 5373091281752496

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0285Witness : Array ℤ :=
  #[-180, -312, -121, 368, -1261, 1074, -37, -1023, 187, 831, 1483, 1417,
  1259, 479, 476, -711, 572, -610, 262, 1473, 871, 507, -72, 553, -450,
  -1803, -511, 409, 1326, -413, -791, 676, -458, 709, 317, -637, -50, -799,
  637, 49, -754, -565, -557, -175, -531, 222, 0, 470, -704, 116, -57, 1330,
  989, 316, 1799, 1092, -478, 1338, -1646, -1352, 738, 531, -1359, -1077,
  -1453, -1796, -1212, 897, 313, 1206, 13, 800, 1331, -1663, -65, -1136,
  -1089, 891, 1391, -1143, -197, -173, 377, 222, 1415, 1035, 1229, -692,
  -198, 278, -514, -308, 1303, 736, -849, 382, 497, -361, -1460, 576, 617,
  1050, -984, 745, 2084, 209, -186, 1520, -1385, -923, -2628, -554, -969,
  173, 849, 970, 1559, 0, 560, -278, 346, -615, 54, 262, -605, 346, -1019,
  750, -1291, 688, 664, -27, -446, 702, 683, 343, 472, -62, 620, 0, -625,
  -1420, 1375, 688, -1480, 423, -196, 1215, -664, 370, 880, 1057, -244, 6,
  -1433, -1334, -608, -1005, -1752, -597, -140, 1382, 973, 1140, 714, 791,
  -3263, 557]

theorem fractionalNearFrameSubtreeG2R0285_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0285Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0285Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0285Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0285_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0285LowerBoundTable : List ℤ :=
  [-821, 173, -2570, 32, 32, 1282, 1621, 703, 1950, 99, 101, 1654, 1684,
  -94, -709, 948, 4027, -3413, 2407, 1477, 3600, 461, -238, 4459, 98]

def fractionalNearFrameSubtreeG2R0285LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0285Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0285LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
