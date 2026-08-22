import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0006`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0006Mask : ℕ := 254737331970565

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0006Witness : Array ℤ :=
  #[2521, 1868, 1458, 1116, 1799, 442, -754, -1140, -484, -2334, -1969,
  -2206, -23, -140, 106, 11, 0, -211, -711, 0, -69, -987, -462, 918, 510,
  10, -1712, -690, -1900, 1593, 1328, 1397, 2362, 18, -325, -293, -1107,
  -463, 635, 246, 839, 800, -318, 454, -607, -308, 1412, 687, -40, 593,
  1287, 58, -252, -900, -716, -943, 766, 788, -808, -924, 97, 79, 1050, 839,
  -334, 323, 113, -351, -261, -470, -110, -11, 401, -259, 1100, 811, 1001,
  -363, -704, -1149, 78, 841, 270, 749, 605, 1137, -126, 136, -307, 94,
  -893, -716, -152, 367, 918, 255, -621, 148, 625, -1330, -122, -452, 475,
  721, 1169, -215, 141, -397, 162, 649, -311, -446, -2012, -1416, -1710, 37,
  -282, 547, -65, 644, 584, 875, -344, -822, 238, 451, 380, -757, -604, 680,
  -654, 229, 324, 367, -283, -429, -238, 352, 1247, 610, 160, 472, 132, 451,
  -153, -721, 611, 82, 131, 459, 466, 330, 399, 684, -555, -636, -23, 102,
  -679, -126, -586, 867, 597, -1164, -114, 149, -765, 183]

theorem fractionalNearFrameSubtreeG2R0006_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0006Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0006Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0006Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0006_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0006LowerBoundTable : List ℤ :=
  [-650, -425, -1199, 1075, 342, 32, 1184, 1635, 1465, 996, 101, 2022, -927,
  517, 1544, 1061, 100, 3606, -135, 3294, 99, -1098, 99, 99, -655]

def fractionalNearFrameSubtreeG2R0006LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0006Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0006LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
