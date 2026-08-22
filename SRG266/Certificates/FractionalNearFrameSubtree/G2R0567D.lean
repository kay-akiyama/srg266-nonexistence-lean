import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0567`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0567Mask : ℕ := 6846468494889618

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0567Witness : Array ℤ :=
  #[-97, 20, -186, -35, 55, 32, -168, 208, 133, -199, -141, 0, 100, 164,
  250, -88, 44, -8, -98, 124, 95, -142, 42, -192, 19, -284, -29, -75, 9, 94,
  117, 74, 356, 83, -43, 0, -41, 87, -32, -56, -30, 14, -173, -147, 122, 79,
  140, 238, -361, 32, 173, 120, -17, 68, -33, 318, 117, 107, -21, -67, -13,
  -314, 89, 44, -213, 76, 167, 143, -1, 31, -25, 82, -62, 37, 124, -225,
  -65, -104, -126, -47, -55, 248, 71, -10, 83, 86, 49, 7, -130, 258, -26,
  129, -129, 77, 8, -137, -253, -379, 228, -27, 183, -40, 8, 61, -20, 27, 8,
  -404, 238, 129, 192, 39, -57, -37, 141, 33, 92, 118, 327, -15, 108, 36,
  -190, 54, -60, 36, 147, -73, -95, 94, 81, 126, 115, 289, 53, 68, -193,
  186, -199, -246, -170, 284, 40, 502, 69, 288, -42, 40, 6, -63, -216, 74,
  -8, -22, -61, 0, -122, -55, 17, 24, -154, 44, 43, -178, 201, -284, -111,
  -8]

theorem fractionalNearFrameSubtreeG2R0567_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0567Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0567Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0567Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0567_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0567LowerBoundTable : List ℤ :=
  [-56, 83, 248, -213, 69, 322, 1, 333, -135, 893, 354, 485, 10, -3, 468,
  567, -675, 63, -110, 16, 731, -106, 11, 833, 911]

def fractionalNearFrameSubtreeG2R0567LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0567Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0567LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
