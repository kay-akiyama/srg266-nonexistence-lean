import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0508`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0508Mask : ℕ := 5811770116772208

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0508Witness : Array ℤ :=
  #[-193, -83, -158, -8, -21, 148, -131, 61, 46, 0, 27, 55, 207, -115, -153,
  -19, -247, 20, -1, 151, 99, -113, 40, -10, 11, -13, 126, -71, 93, -139,
  -72, -81, -171, -28, 0, 62, 37, 203, -55, -54, 53, 44, 2, 38, -142, 25,
  -22, 86, -56, -46, 97, 13, -47, -219, 92, 45, -90, -105, -181, 125, 48,
  84, 40, -21, -24, 165, 41, 149, -57, 34, 149, -75, -57, -73, -15, -199,
  -53, -34, -24, 56, 41, 53, -115, -82, -29, -27, 15, -118, 38, -25, 3, 54,
  -161, 23, 61, -3, 197, 30, 10, 28, 25, 62, 264, -30, -146, 239, -69, 34,
  124, -79, -57, -173, -337, 47, -178, 16, 19, 76, 7, -22, 1, 136, -141,
  -209, -110, -130, -26, 118, 53, 74, 151, -102, -18, -75, -121, 31, 7, -97,
  -24, 204, 105, 19, -32, 87, 235, 49, 48, -51, 84, 146, 68, 69, 42, -67,
  -79, 15, -90, -149, -192, -17, -187, 37, 68, 233, 76, -159, 26, 92]

theorem fractionalNearFrameSubtreeG2R0508_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0508Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0508Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0508Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0508_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0508LowerBoundTable : List ℤ :=
  [-219, -22, -150, 48, 3, 2, -257, 45, -83, 132, 362, 38, -342, -614, -230,
  214, 9, 197, 92, 9, 79, 142, -70, -2, 24]

def fractionalNearFrameSubtreeG2R0508LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0508Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0508LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
