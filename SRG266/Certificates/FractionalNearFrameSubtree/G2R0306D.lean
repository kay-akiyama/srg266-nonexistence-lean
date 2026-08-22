import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0306`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0306Mask : ℕ := 5387247644529304

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0306Witness : Array ℤ :=
  #[503, 255, 543, 673, 21, 104, 355, 755, 225, 98, -527, 53, -604, -38,
  -26, -403, 131, 30, -215, -137, -117, 219, 211, -276, 339, 483, 515, 27,
  34, 777, 26, -63, -438, -206, -670, -49, 8, -113, 23, -10, -492, 429, 91,
  -132, -157, -269, 6, 359, -666, -19, 182, 53, -177, 371, 224, -685, -346,
  -482, 1402, 895, -180, 611, 542, 755, 984, 141, -196, 82, 0, -708, -468,
  427, -1291, -93, 197, 44, -29, -627, -253, -825, -557, 172, 845, -261,
  -36, -274, -65, -121, -317, 192, -62, -36, 574, 1039, 430, 372, -230, 383,
  -51, -259, 98, -332, -90, 298, 540, 273, 300, -240, 568, 169, -457, 381,
  568, -435, -123, -48, -500, -152, 607, 115, -79, -226, -117, -156, -380,
  454, 161, 182, 84, 102, -42, 277, 18, 113, -522, 468, -285, 211, 643, 758,
  57, -125, -228, -699, 757, -340, 433, -162, -566, 461, 134, -47, 267, 488,
  -609, 142, -825, -417, 193, 210, -692, -66, 621, -1160, 401, -387, 0, 400]

theorem fractionalNearFrameSubtreeG2R0306_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0306Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0306Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0306Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0306_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0306LowerBoundTable : List ℤ :=
  [-93, 31, -186, 1495, -584, 33, 32, 1202, 32, 2943, -1225, 1101, -99, 100,
  675, 1719, 1775, 556, -39, 1781, 2494, -1318, 755, 635, 1016]

def fractionalNearFrameSubtreeG2R0306LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0306Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0306LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
