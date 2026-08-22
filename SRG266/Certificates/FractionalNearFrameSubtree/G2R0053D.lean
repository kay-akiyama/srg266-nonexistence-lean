import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0053`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0053Mask : ℕ := 936558592639626

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0053Witness : Array ℤ :=
  #[478, 1595, 687, 300, -171, -1152, -378, -628, 0, 635, 811, 249, -123,
  -189, -2481, 0, -815, -417, -13, -379, -1565, 668, -1270, -1121, 470, 256,
  748, 517, 656, -297, 707, -1661, -1508, 413, 950, 1229, 472, 522, 591,
  -447, 1347, 554, 1267, -1117, -1333, 1102, 405, 1215, -1070, -374, 583,
  -1436, -825, 533, 550, 901, -1144, 280, 183, -990, -965, 168, -1573, 831,
  79, -862, 17, 869, 777, 1008, -688, -269, 1280, -73, 146, -150, -1149,
  -1206, 357, 702, 705, 790, 1173, -169, 147, 408, 316, -423, -578, -180,
  -54, 2511, -165, -94, -359, -907, -842, 1820, 341, 1225, 278, 2000, 1493,
  -853, 192, 677, 1789, -312, 1211, 1505, -1056, -2687, -590, -766, -1281,
  -313, 513, 84, 353, 646, -1352, 67, 1225, 635, 820, 469, 224, -1202, 573,
  1303, 850, -305, 1493, 1117, -1149, 1261, -366, -652, 366, -539, 465,
  -1184, -59, 853, 207, -1022, -627, -954, -294, 34, -1259, 161, 452, -1013,
  -362, 914, 662, -41, 1202, -653, 1829, -644, 603, 438, -919, 1384, -552,
  -506]

theorem fractionalNearFrameSubtreeG2R0053_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0053Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0053Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0053Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0053_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0053LowerBoundTable : List ℤ :=
  [-73, 1003, 2359, 984, -2440, -279, 335, 32, 1820, 698, -1271, 1451, 1154,
  4000, 4454, 1303, 1664, 844, 151, 1139, 2486, 97, 101, 3550, 1818]

def fractionalNearFrameSubtreeG2R0053LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0053Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0053LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
