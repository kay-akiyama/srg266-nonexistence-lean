import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0030`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0030Mask : ℕ := 1366260541268227

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0030Witness : Array ℤ :=
  #[458, -144, 7, -142, -103, 2, 154, -257, -127, 0, 15, 127, -146, 23, -80,
  384, 171, -71, 261, -406, 23, 367, 334, -130, -97, 466, 530, -270, 36,
  -661, -43, -231, 191, 155, -62, -40, 120, 240, 7, 108, 258, -259, -151,
  -176, 298, 95, -149, 76, 258, -213, -71, -21, 8, 68, 236, -372, -198, -10,
  261, -11, -170, 153, 216, 164, -379, 421, 98, -147, -116, 3, -366, -259,
  76, -21, 428, 20, 373, 124, -111, 72, 195, 416, 561, -301, -229, -90, 389,
  458, 112, -97, 109, -2, -49, 64, 91, 141, -220, 378, -87, -190, -172, 165,
  -238, -215, -251, -44, 87, -241, -172, 176, -230, 91, 334, -15, 80, 88,
  132, -154, -288, -470, -433, -210, -107, 84, 157, 318, -437, 38, 87, -251,
  0, -32, 175, -598, 368, 126, -394, 73, -80, 287, 349, -543, -323, -361,
  -483, -207, 64, 396, 256, -186, -305, -302, 19, -403, 133, 271, 33, -433,
  -425, -78, 417, 157, 640, -21, 395, 405, -76, 201]

theorem fractionalNearFrameSubtreeG5R0030_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0030Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0030Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0030Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0030_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0030LowerBoundTable : List ℤ :=
  [-210, -496, 435, 2, 2, 437, 2, 120, -129, 129, -840, 210, -666, 605, 842,
  251, 866, 325, -937, -910, -708, 1054, 1078, 583, 98]

def fractionalNearFrameSubtreeG5R0030LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0030Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0030LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
