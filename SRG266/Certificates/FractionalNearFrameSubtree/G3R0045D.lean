import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0045`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0045Mask : ℕ := 957317352557218

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0045Witness : Array ℤ :=
  #[882, 832, 1197, 2865, 670, 1460, -1117, 647, 234, -710, 115, 1107, -40,
  -173, -514, -1908, -168, 1677, -189, -740, 2976, 713, -734, -568, -697,
  -482, -197, 0, 679, -1041, 1331, -461, -1041, 1049, 854, -12, 373, 649,
  254, 278, -7, 130, 417, -620, -757, 677, 259, 606, -585, -150, -557, 1174,
  317, -252, 1307, -1160, -515, -643, 1115, 172, 1502, 1005, 891, 857, 1166,
  -1243, -172, 1642, 1495, -494, -277, 495, 70, 391, 1249, 2057, -202, -90,
  -1822, 162, -2394, -909, -2446, -1712, 46, 765, 588, 1332, -1077, -20,
  -110, 849, -1002, 136, 1547, 1429, 207, -298, -82, 189, -625, -333, 391,
  1283, 721, 944, 1294, 618, 856, -149, -23, 0, -3009, -2853, -743, -1547,
  -494, 638, 60, 298, 1122, 1908, -1575, -174, 695, 685, 518, 696, 960,
  2118, 1136, 625, -1411, -339, -938, 3707, -905, 539, -479, 1098, 956, 327,
  -204, -269, -572, 688, 44, -283, 1958, 265, -687, 188, 350, 166, 820, -27,
  -705, 1313, 1498, 224, -1460, 280, 762, -403, 510, 502, -93, -1327]

theorem fractionalNearFrameSubtreeG3R0045_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0045Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0045Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0045Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0045_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0045LowerBoundTable : List ℤ :=
  [1234, 2163, -459, 1894, -425, 1284, 4273, 1329, 3101, 890, 5760, 2658,
  2534, -2854, 4858, 461, 820, 4586, 4365, -2324, 5698, 6350, 1709, 5544,
  4812]

def fractionalNearFrameSubtreeG3R0045LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0045Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0045LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
