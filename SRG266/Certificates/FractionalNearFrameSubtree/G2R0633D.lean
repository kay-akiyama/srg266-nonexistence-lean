import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0633`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0633Mask : ℕ := 11341147604751882

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0633Witness : Array ℤ :=
  #[-19, 290, -54, -93, 37, 130, -153, 184, -244, -158, 195, 116, 157, 209,
  -76, -117, 20, 143, 78, 10, 469, -174, 243, 114, 18, 98, -247, -216, -339,
  90, 22, -135, -50, -49, 157, -37, 412, -14, 139, 17, -16, 133, 46, 323,
  33, 95, -67, -31, -47, 129, -28, -40, -247, 256, 149, -4, 116, -31, 51,
  229, -50, -131, -101, 147, -126, 461, 292, -7, -375, 104, -43, -145, 27,
  53, 134, 410, -325, -57, 86, 34, 204, 15, -262, 391, -82, -282, -241, 23,
  208, 418, 107, 111, -134, -108, -219, -242, 233, 164, 116, -23, -184, 88,
  180, 77, 322, -229, -32, -255, -90, -495, 116, -240, 207, 146, -49, 102,
  10, 57, -152, -245, -187, 461, -77, 51, -34, -162, 209, 55, 186, -21, 268,
  421, 159, 124, 135, -94, 180, -338, 415, -671, -18, -178, -18, 335, 70,
  -183, 86, -151, -262, 75, -138, 15, -222, 31, 130, 270, 30, -146, 52, 531,
  244, 159, -244, 216, 477, 193, 25, 252]

theorem fractionalNearFrameSubtreeG2R0633_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0633Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0633Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0633Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0633_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0633LowerBoundTable : List ℤ :=
  [250, 259, 951, 102, -52, 527, 314, 551, -284, 888, 1009, 473, -286, 1023,
  814, 966, 667, 402, 909, -192, -418, 809, -609, 306, 747]

def fractionalNearFrameSubtreeG2R0633LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0633Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0633LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
