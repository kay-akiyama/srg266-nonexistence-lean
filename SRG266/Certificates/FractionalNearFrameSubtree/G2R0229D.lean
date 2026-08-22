import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0229`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0229Mask : ℕ := 2502107843204242

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0229Witness : Array ℤ :=
  #[997, 954, 488, -234, 188, -770, -489, -412, -995, -561, 679, 762, 280,
  534, 1181, 207, 877, 768, -6, 465, -1898, -19, 814, 173, 288, 408, 377,
  -717, 149, -434, 337, 741, -1207, 256, 383, 344, 18, -329, -123, -135,
  -120, 75, 768, 875, 331, 229, 60, -130, -602, -152, 330, -65, -1689, 1365,
  94, 446, 722, -340, 0, 147, 284, 1148, 82, 471, 63, -1391, 43, 378, -149,
  286, -198, -825, -337, 659, 2180, -564, -1003, -1261, -548, 1079, 1008,
  151, 309, -209, 0, -553, -548, -1006, -92, -377, 1325, 240, 709, 224,
  -270, 37, 570, -288, 334, 2436, 938, 1380, 1283, 2311, 949, -144, -311,
  429, 811, 494, -456, 274, 285, 222, -551, 767, 270, 376, 1043, -17, 325,
  986, -1056, -960, 177, 96, -139, 191, -856, 434, 1316, 749, 28, 327, -425,
  572, 1006, 152, -4, -2, -53, 643, -209, 455, -15, -199, 126, -197, 1188,
  480, -428, 0, 340, 436, -1411, 209, -1242, -617, 447, -1044, -312, -130,
  540, -696, 289, -944, -1458, -1142]

theorem fractionalNearFrameSubtreeG2R0229_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0229Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0229Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0229Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0229_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0229LowerBoundTable : List ℤ :=
  [564, -472, 1681, 7, 754, 2618, 32, 1749, 1771, 2324, 52, 1948, 382, 8809,
  2721, 3354, 99, 377, -435, 98, 2226, 1858, 2296, 2076, 6467]

def fractionalNearFrameSubtreeG2R0229LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0229Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0229LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
