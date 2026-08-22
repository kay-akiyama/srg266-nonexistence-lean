import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0086`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0086Mask : ℕ := 1212602044358915

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0086Witness : Array ℤ :=
  #[0, -26, -325, -326, -170, -377, 454, 257, 51, 1, 73, -207, 505, 0, 284,
  114, -135, 182, 625, 95, -123, -238, -219, -731, 275, 48, 0, 103, -327,
  222, 210, 168, 630, 112, 498, 175, -145, -12, 44, 411, 83, 146, -302,
  -230, -41, -68, -396, 0, -383, 563, 282, 163, -140, -55, 25, -8, -346,
  -225, -454, -271, 83, 692, 244, 169, 87, 20, 14, -64, 190, 152, 76, 227,
  -140, 313, -155, -104, 248, 62, 284, -35, 705, -1, 207, 57, -88, 429, 15,
  112, 58, 201, 313, -163, 197, -34, 7, 101, 50, 2, 20, 293, -140, -432,
  -117, 312, 84, 204, -137, 224, 106, 436, 164, 62, -44, 218, 52, 327, -236,
  307, -60, -375, -396, -360, 113, 316, 137, 56, -18, 177, -187, 320, -1,
  104, 262, -131, 419, 108, 254, 22, -40, 301, 161, 358, 111, 73, 119, 42,
  -358, 66, -58, 213, 65, 291, -101, 126, 14, 62, -447, 186, 406, 198, -128,
  91, 28, 82, 182, -63, -266, -88]

theorem fractionalNearFrameSubtreeG2R0086_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0086Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0086Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0086Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0086_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0086LowerBoundTable : List ℤ :=
  [261, 341, 942, 642, 501, 208, 519, 1073, 1420, -312, 1206, 682, 1117,
  1748, -198, -207, 1587, 427, 4, 763, 1847, 10, 506, -758, 1497]

def fractionalNearFrameSubtreeG2R0086LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0086Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0086LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
