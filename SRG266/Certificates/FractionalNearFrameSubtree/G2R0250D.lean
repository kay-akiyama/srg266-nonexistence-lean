import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0250`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0250Mask : ℕ := 5354469853861382

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0250Witness : Array ℤ :=
  #[-104, -24, -3, 70, -14, 0, 11, 0, 33, -24, 58, 39, 15, 21, 141, -44, 0,
  59, 13, 14, 115, 19, 22, -55, 38, 2, 88, 0, -75, 28, 5, 20, 34, 36, -8,
  -13, 55, -23, 18, 37, 10, 10, 89, 111, 45, 64, 61, 25, -43, 18, -4, -2,
  -10, 88, 44, -10, 78, 11, -63, -97, -7, -16, -15, -31, 40, 25, -27, 86,
  -103, -34, 4, -26, 21, 56, -41, 42, 78, 57, 71, -42, -36, -61, 20, -81,
  39, -65, -19, -62, 47, 27, 53, 33, 9, 91, -18, 29, -131, 79, 29, -62, -37,
  50, 76, -13, 76, 247, -48, -1, 29, 38, 110, -21, -36, -171, -72, 178, -47,
  -24, 14, -11, -54, -11, 0, -115, -89, 81, 82, 37, 89, 155, -101, 4, 51,
  17, 34, -173, -57, 42, 24, -29, 92, 33, -23, 46, 81, 45, 97, 6, -115, -35,
  34, 70, 113, -63, -76, -39, 76, -53, -87, -7, 75, 44, -89, -116, 123, 77,
  -48, -18]

theorem fractionalNearFrameSubtreeG2R0250_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0250Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0250Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0250Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0250_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0250LowerBoundTable : List ℤ :=
  [114, 3, 172, 303, 119, -14, 270, 181, 3, 10, 212, 381, 11, 394, -29, 64,
  273, 111, -47, 9, -71, 377, -79, 7, 105]

def fractionalNearFrameSubtreeG2R0250LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0250Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0250LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
