import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0618`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0618Mask : ℕ := 9648062760076550

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0618Witness : Array ℤ :=
  #[3, 49, -45, -52, -39, 4, -265, 60, 19, -55, -12, 12, 157, 140, 65, 351,
  246, 272, 259, 198, 302, -351, 79, -29, 11, 3, -30, -278, -101, -153,
  -157, 0, 192, 69, 128, 72, -36, -5, -22, 92, -50, 60, -10, -96, -170, -14,
  42, -4, -58, 15, 72, 20, 0, 130, -110, 84, 10, 45, 52, -7, -47, -10, -34,
  -29, -42, -102, 29, 25, 41, 42, 130, 139, 0, 99, 40, -45, -19, -16, -27,
  -52, 190, 23, -63, 107, 30, -4, 67, 157, 50, 20, -97, 76, 25, -14, 106,
  76, 19, -6, 67, -177, -59, -66, -18, 48, 141, -76, 79, -116, 39, -168,
  187, 287, 89, 109, 26, 142, 176, 53, 236, 78, 61, -36, 4, -8, 0, 126, -98,
  110, 110, -31, 0, 91, 53, 26, 72, -51, 56, -44, 106, 140, -210, 136, 149,
  -206, 107, 50, 20, 117, 59, 143, 146, 60, 56, 43, -5, 149, 14, -49, -10,
  -44, -51, 121, -41, -2, -55, 108, -65, -162]

theorem fractionalNearFrameSubtreeG2R0618_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0618Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0618Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0618Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0618_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0618LowerBoundTable : List ℤ :=
  [243, 281, 56, 266, 521, 441, 225, 2, 354, 946, 446, 355, 740, 665, -40,
  10, 2, 543, 379, 265, 261, 658, 366, 545, 65]

def fractionalNearFrameSubtreeG2R0618LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0618Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0618LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
