import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0169`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0169Mask : ℕ := 1380465583231588

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0169Witness : Array ℤ :=
  #[-248, -608, -754, -551, -798, -86, 631, -140, 419, -26, 838, 785, -24,
  534, 498, 420, 1085, 312, 314, 249, 40, -172, 138, -265, -388, -202, 236,
  85, -173, 161, 32, 796, 320, 884, -323, 123, -75, -715, 124, -366, -506,
  -561, 0, -505, -150, -290, -95, 9, 341, 366, 441, 553, -187, -348, -404,
  0, 261, 216, 86, -215, -53, -104, 180, 372, 0, 88, -304, 66, 82, 199, 403,
  371, -591, 128, -83, 525, 82, 147, -86, -64, 374, 238, -111, -342, -225,
  175, 556, 73, -333, 261, 348, 460, -416, 50, 401, -444, 271, -356, 8, 44,
  -39, -2, 584, -202, 345, -266, 716, -583, -709, -469, 40, 384, 127, -19,
  511, 665, -454, -292, -472, -166, -200, 568, 192, 366, -98, -495, -69,
  294, 546, 217, 355, -391, -251, -516, 305, 225, 603, 134, 190, 228, 178,
  595, -176, 60, 509, 367, 203, -133, 140, -445, 234, -166, -349, 263, -662,
  614, -358, 377, -285, 267, -88, -295, -466, 276, 274, 35, 436, -410]

theorem fractionalNearFrameSubtreeG2R0169_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0169Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0169Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0169Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0169_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0169LowerBoundTable : List ℤ :=
  [167, 32, 33, 262, 955, -4, 1077, 534, 32, 442, 1686, 982, 1604, 764,
  3349, 539, -620, 1082, 27, 2254, -492, 572, 1547, 818, 962]

def fractionalNearFrameSubtreeG2R0169LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0169Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0169LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
