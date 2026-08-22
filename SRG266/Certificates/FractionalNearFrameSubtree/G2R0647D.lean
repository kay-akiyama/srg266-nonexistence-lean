import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0647`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0647Mask : ℕ := 36115353394995721

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0647Witness : Array ℤ :=
  #[-652, -965, -765, -593, -1425, 0, 1291, 1488, 646, 1493, 938, 2426,
  -680, 262, -312, 406, -420, -1310, 1062, -236, 192, 42, -522, -49, -341,
  -276, -526, -775, 1032, 2428, -91, 490, 770, 756, 457, 742, -70, -467,
  -268, -963, 719, 338, -499, -358, -1425, -54, -316, -330, 199, 115, 120,
  -282, -40, -729, 408, 515, 833, 603, -265, 123, 436, 603, 138, -292, -153,
  -594, -809, -474, 359, 942, -85, 382, 403, 730, -67, 371, 445, -522, -349,
  64, 207, -289, 13, -22, 902, 398, -287, 815, 154, 183, 93, 264, -170,
  -112, -506, 257, 1306, 926, -15, 50, -291, 400, 1275, 193, 273, -649, 558,
  -152, -571, -135, -795, -149, 22, -352, -619, 1556, -538, 4, 236, 347,
  336, -119, 281, -224, -1077, 191, 296, 863, 115, -167, 194, -271, -537,
  -596, -103, 460, 1061, -36, 169, 470, -245, 403, 290, -483, 178, 181,
  1051, 459, 146, 253, 630, 452, -92, 0, 335, 501, -371, 234, -1682, 865,
  117, -50, -557, -1499, 683, 365, -787, -1013]

theorem fractionalNearFrameSubtreeG2R0647_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0647Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0647Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0647Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0647_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0647LowerBoundTable : List ℤ :=
  [564, 33, 31, 1405, 1294, 1364, 34, 560, 2285, 100, 487, 1899, 2001, -422,
  1097, 1799, 2377, 100, 101, 707, 430, 1376, 2982, 1140, 2274]

def fractionalNearFrameSubtreeG2R0647LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0647Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0647LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
