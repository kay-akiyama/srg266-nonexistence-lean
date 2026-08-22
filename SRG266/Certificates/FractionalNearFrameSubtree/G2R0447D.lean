import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0447`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0447Mask : ℕ := 5791999860069016

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0447Witness : Array ℤ :=
  #[-42, -94, 73, 66, 12, 12, 51, 111, 144, 65, -79, -52, -13, -36, 51, 39,
  7, 31, 64, 4, 22, -91, -60, -30, -65, 162, 23, 2, 10, -52, -86, 54, -24,
  120, -21, 104, -88, -97, 0, 16, 19, -31, 29, 49, -13, -41, -70, 33, -39,
  63, -36, 152, 42, 281, 134, 26, 43, -8, -128, -52, 42, 28, 70, -65, 38,
  -11, 171, -68, 60, 179, 100, -160, 10, -64, -89, 96, 98, 65, 16, -57,
  -147, 98, 73, -160, 202, -97, -128, 16, 7, -198, -76, -103, 44, 27, 15,
  -7, -32, 85, -10, -40, 0, 57, 74, -90, 27, -60, 14, 32, 119, 62, 52, -137,
  -2, -7, 108, -75, -29, 146, -77, -107, -66, 60, -1, 97, -43, 80, -20, -2,
  -8, 113, -15, 67, 117, -67, -51, 108, -120, -36, -26, -186, 104, -43, -30,
  104, 70, 167, -63, 143, 33, 82, 55, -3, 12, 31, 11, 226, 203, -60, 44,
  -107, -119, 163, -48, -5, -82, -4, -2, 46]

theorem fractionalNearFrameSubtreeG2R0447_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0447Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0447Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0447Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0447_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0447LowerBoundTable : List ℤ :=
  [34, 181, -20, 204, -143, 150, 63, 133, 203, 622, 23, 4, 300, 10, -171,
  -141, 523, 218, 199, 759, 176, 8, 266, 71, 427]

def fractionalNearFrameSubtreeG2R0447LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0447Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0447LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
