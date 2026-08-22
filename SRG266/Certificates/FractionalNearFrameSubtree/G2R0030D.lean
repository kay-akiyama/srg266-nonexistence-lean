import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0030`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0030Mask : ℕ := 830728957575768

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0030Witness : Array ℤ :=
  #[-115, -320, -359, 55, -441, 118, -144, -311, -768, -283, 545, 293, 244,
  601, 373, 276, -242, 126, 533, 329, 90, 406, 283, -539, -121, -329, 122,
  -200, -80, 63, 1401, 1090, 104, -716, -57, 436, 263, 296, 593, -726,
  -1237, -1068, 655, -465, 1131, 966, -101, -447, 255, 348, 324, -218, -333,
  622, -519, -297, 353, -205, -76, 500, 298, 285, 344, -227, -610, -338,
  377, -335, -127, -247, 37, 84, -105, 250, 787, -343, -423, 305, 535, -822,
  133, -436, 362, 422, -936, -793, 192, -507, -463, 133, 174, 422, 306,
  -754, -326, -9, -528, -69, -39, -498, 195, -764, -184, -847, -82, -595,
  962, 520, 167, 91, -453, -886, 0, 481, -314, 243, -993, -295, -850, -493,
  640, 277, -28, -182, -350, -127, -486, 173, -74, 234, -169, -11, -105,
  659, -124, 384, -704, -296, 567, 563, 302, 80, -526, 29, -493, -225, -165,
  1186, -59, 235, 398, 717, 475, 497, 215, -205, -608, -414, 199, -745, 218,
  -352, -177, -103, -33, -48, 112, -451]

theorem fractionalNearFrameSubtreeG2R0030_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0030Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0030Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0030Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0030_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0030LowerBoundTable : List ℤ :=
  [-857, -243, 31, 32, -1232, 248, 144, -303, -744, -651, -1140, 127, 452,
  884, 883, 1299, -2911, 100, 101, -1054, 564, 698, -1417, 1174, 1389]

def fractionalNearFrameSubtreeG2R0030LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0030Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0030LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
