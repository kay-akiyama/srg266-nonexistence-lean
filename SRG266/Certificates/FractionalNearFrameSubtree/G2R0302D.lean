import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0302`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0302Mask : ℕ := 5387217096248408

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0302Witness : Array ℤ :=
  #[-108, -139, 35, 23, 122, -293, 210, -159, -51, 0, -3, 212, 209, 174,
  -18, -104, 39, 201, 22, -280, -61, 65, -54, 26, 73, 97, 132, 95, 219, 175,
  -74, 205, 0, -108, -32, 46, 252, -382, -170, -70, 341, 142, 16, -16, -32,
  147, 77, -137, 93, 17, 111, 21, -94, 74, -30, 138, 238, -109, -189, 89,
  205, -313, 43, 96, 6, -315, 129, 143, -21, -87, 0, -114, -199, 21, -27,
  161, 111, 70, -380, 113, -71, -11, -57, -29, 161, -16, -240, -18, 10, 11,
  78, 2, -106, 81, 97, -323, 135, -136, -119, 6, -171, -6, -226, 78, 61,
  -200, -307, 144, 202, 152, 102, -34, 483, 6, 130, 229, 116, 245, 300, 258,
  110, -90, -226, 68, 186, 210, 102, 131, -55, 9, -41, 15, 257, 214, 48,
  189, 84, 25, -195, 168, 99, -78, -107, -99, -65, 35, 5, 89, -70, 0, -89,
  106, 177, 0, -34, -101, -42, -103, -205, 52, 112, -33, 219, -142, 129, 31,
  -306, -168]

theorem fractionalNearFrameSubtreeG2R0302_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0302Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0302Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0302Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0302_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0302LowerBoundTable : List ℤ :=
  [18, 276, 2, 2, 112, 343, 298, 306, 3, 879, 654, 987, 259, 33, 43, 9, 835,
  8, -270, -138, 337, -422, 827, 240, -41]

def fractionalNearFrameSubtreeG2R0302LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0302Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0302LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
