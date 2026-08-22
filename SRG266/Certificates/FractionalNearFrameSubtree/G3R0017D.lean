import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0017`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0017Mask : ℕ := 829707305533842

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0017Witness : Array ℤ :=
  #[-120, 30, -58, 39, -34, 6, -1, 26, 0, 76, 81, 15, 15, -45, -43, -11,
  -48, 88, 47, -12, 80, -3, -23, 8, -8, 76, -27, -29, -100, 0, -70, -50,
  -58, -4, -36, 58, 44, -10, 2, -22, 44, 111, 0, 81, 30, 24, -6, -47, -111,
  -7, 33, -57, 25, -60, -43, -67, -22, -18, -17, 16, 90, 27, 56, -7, -63, 4,
  -50, -9, -41, -1, 6, 20, 0, -48, -46, -1, 17, -49, 43, -4, 0, 1, -76, -40,
  -83, -80, -35, -34, -10, 59, 6, -52, -30, 11, 26, -32, 30, -21, -17, 19,
  104, 27, -11, -13, -63, -39, -6, 43, -75, -14, 4, 8, 60, 7, -57, -34, -32,
  -1, 22, -71, -21, -42, -41, 13, 1, 73, -76, -15, 12, 56, 22, -1, 33, -28,
  -39, -27, 24, -64, -67, 43, -74, 4, 39, -9, 0, -54, -44, 53, 15, 2, -24,
  -42, -37, 6, 48, -26, 66, -24, -23, 45, -4, 41, 49, 121, 41, -16, 40, 38]

theorem fractionalNearFrameSubtreeG3R0017_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0017Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0017Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0017Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0017_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0017LowerBoundTable : List ℤ :=
  [-98, 2, -104, 27, -83, 1, -44, -65, -125, 17, -167, -16, 120, -137, -78,
  -152, 76, 115, 138, 82, -262, 156, -86, -15, -155]

def fractionalNearFrameSubtreeG3R0017LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0017Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0017LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
