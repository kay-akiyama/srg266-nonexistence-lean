import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0120`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0120Mask : ℕ := 5389583956646320

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0120Witness : Array ℤ :=
  #[-82, -159, 342, -95, -176, 7, 543, 92, 263, -17, 324, -310, 244, 73,
  188, -186, 946, 317, 448, -296, -106, 389, 0, 677, -292, -381, -483, 110,
  -169, 461, 99, 269, 0, -287, 264, -156, 77, -178, -93, 0, 66, 235, 35,
  335, -555, 124, -6, -532, 279, 362, 121, 86, 604, 332, 622, 423, -141,
  -237, 211, -432, -317, 51, -140, -731, -197, -99, 97, 384, 191, -91, -519,
  55, 355, 235, -27, -156, 0, 165, -304, 179, 107, 198, -318, 411, -462,
  -360, 63, -206, -366, -723, -51, 677, 155, 716, 116, -106, 1, -254, -595,
  482, 58, -170, 13, 377, 12, -44, 186, -229, 86, 22, -60, 44, -229, 373,
  233, 316, 759, -175, -97, 44, 341, 217, 623, 237, -25, -51, -223, -383,
  -284, -276, -54, -67, 75, 383, -173, 130, 162, 150, 44, -99, -1, 309, 238,
  685, 226, 0, 8, 482, 157, 146, 236, 530, 300, -373, -258, -136, -138, 29,
  -105, 102, 121, 193, 296, 327, 407, 244, -535, -67]

theorem fractionalNearFrameSubtreeG3R0120_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0120Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0120Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0120Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0120_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0120LowerBoundTable : List ℤ :=
  [313, 1053, 768, 32, 539, 458, 131, 1169, 707, 2219, 716, 999, 101, 2134,
  182, 1616, -373, 729, 1267, 1360, 99, 497, 1022, 283, 841]

def fractionalNearFrameSubtreeG3R0120LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0120Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0120LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
