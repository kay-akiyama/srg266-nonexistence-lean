import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0083`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0083Mask : ℕ := 899223966167329

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0083Witness : Array ℤ :=
  #[-139, 0, 39, -36, -193, -145, 9, 78, 97, 244, 177, -35, 68, 35, -145, 0,
  -94, 49, -113, -60, 24, 110, 5, -215, -103, 121, 102, 107, -90, 36, -37,
  -46, -6, -85, -242, -97, 40, -10, 46, -13, 121, 114, 35, 106, 279, -230,
  -262, -202, 96, 1, 94, 135, 108, 43, 68, 58, 30, 91, 177, -28, -95, 50, 9,
  -82, 23, 2, 27, 9, 38, 132, -43, 147, -57, 14, 44, -24, -35, 120, 4, 67,
  63, 31, 14, 46, 68, 114, 26, 31, 191, 153, 78, 95, 102, 149, 129, 108,
  146, 90, 63, 96, -2, 55, 27, 38, 41, 94, 73, -66, 246, 154, 39, 12, -47,
  70, 19, 37, 24, 223, -27, -75, -90, 68, 57, -252, 67, 131, -13, -28, -51,
  27, -44, -327, -66, -4, -60, -72, 93, -56, -128, -49, -46, -47, 0, 1, -69,
  -13, -84, 16, -11, -59, -85, -30, -15, 123, -58, 67, 53, 214, 12, -23,
  100, 74, 27, -5, 141, 19, 237, -205]

theorem fractionalNearFrameSubtreeG1R0083_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0083Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0083Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0083Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0083_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0083LowerBoundTable : List ℤ :=
  [134, 2, 597, 3, 132, 129, 207, 122, 341, 52, 161, -76, 162, 733, 474,
  127, 656, 354, 83, 433, 187, 10, 294, 356, 10]

def fractionalNearFrameSubtreeG1R0083LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0083Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0083LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
