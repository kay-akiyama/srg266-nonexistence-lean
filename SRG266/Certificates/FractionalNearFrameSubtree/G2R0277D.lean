import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0277`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0277Mask : ℕ := 5372473410442764

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0277Witness : Array ℤ :=
  #[79, 107, 86, 275, 11, 12, -68, 109, 63, -30, 156, 131, 48, 272, 181,
  -210, 117, 29, 147, 206, -83, 99, 57, 75, 39, 76, -161, -63, -166, -1,
  -23, 250, 175, 91, -64, -184, 201, -12, -167, 65, -183, -179, -108, -156,
  -50, -18, 89, 211, 70, 233, -106, -358, -296, -68, 348, -134, -16, -58,
  16, 43, -53, -151, 13, 53, 28, 179, 23, 69, 103, -10, -156, -51, 15, -273,
  -508, 35, 46, 89, 41, -93, 168, 15, -159, 109, -240, 26, 61, -5, 44, -194,
  -78, -288, 381, -28, 120, 12, 41, 290, -27, -196, 41, 70, 110, -22, -30,
  65, -234, -175, 22, 68, 342, -9, 78, -26, 136, -70, 49, 212, 60, -70, -3,
  124, -72, 282, 137, 156, -124, -32, -62, 17, 82, -198, 214, 141, -22,
  -157, 73, 193, 41, 18, -138, 172, -54, -54, -357, 26, 71, 78, -80, -121,
  73, 22, 2, 25, -106, -287, -402, 118, 187, -15, 25, 94, 109, -378, -168,
  307, 140, -12]

theorem fractionalNearFrameSubtreeG2R0277_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0277Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0277Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0277Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0277_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0277LowerBoundTable : List ℤ :=
  [-108, 16, -412, 409, 381, -99, 687, 31, 252, 51, 40, -355, -148, 99, 756,
  -908, 99, 261, 99, 460, 824, 858, 668, 335, 24]

def fractionalNearFrameSubtreeG2R0277LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0277Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0277LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
