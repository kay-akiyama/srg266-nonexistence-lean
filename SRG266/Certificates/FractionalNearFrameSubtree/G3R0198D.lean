import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0198`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0198Mask : ℕ := 6874406780068504

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0198Witness : Array ℤ :=
  #[-59, -27, -18, -31, -73, 138, 60, -6, 134, -11, 45, 24, -3, -69, -50,
  62, 25, -40, 46, 106, 30, -40, 101, -38, -17, -65, -109, -150, -59, -42,
  -80, 101, 107, -16, -15, 1, 12, 15, -28, 53, 105, 62, 104, 6, 69, 30,
  -168, -50, 0, -13, -24, -105, -201, 42, 325, 349, -298, -214, -212, -132,
  43, -264, -211, 0, 32, -238, -107, 223, -374, -139, -176, -135, -3, 43,
  -168, -166, 9, 64, 56, -84, -47, -264, 44, -62, -61, 68, -219, 18, -136,
  -98, -46, -115, -56, -20, -37, 177, 51, 12, -87, -28, -77, -33, -59, -65,
  -18, 220, -24, 354, -77, -11, -118, 225, 18, -138, -254, -12, -20, 248,
  -6, 13, 138, -8, -76, -77, 158, 39, -98, 63, 131, 21, 79, 24, -138, -93,
  0, -9, 23, 127, -72, -187, -123, 78, 181, 28, 46, 100, 57, 35, 65, 25,
  -43, 8, 38, -158, 46, -105, -70, -125, -35, -121, 119, 19, 154, -168, 0,
  -49, -122, -17]

theorem fractionalNearFrameSubtreeG3R0198_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0198Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0198Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0198Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0198_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0198LowerBoundTable : List ℤ :=
  [-410, -76, -212, -287, 3, -226, -412, -170, -230, -71, -212, 453, 892,
  -166, 18, -372, -839, -277, 139, -436, -782, 104, 58, -587, 150]

def fractionalNearFrameSubtreeG3R0198LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0198Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0198LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
