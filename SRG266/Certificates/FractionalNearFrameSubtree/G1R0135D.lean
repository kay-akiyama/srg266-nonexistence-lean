import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0135`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0135Mask : ℕ := 1022439632519570

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0135Witness : Array ℤ :=
  #[-119, -22, -19, -169, -54, 25, 48, 16, 71, 5, 161, 53, 71, 12, -40, 0,
  0, 159, 64, -13, 6, -19, -89, -5, 36, -57, -27, -139, 95, 14, 56, 0, -30,
  30, 183, 28, -141, -139, -12, -40, -3, 25, -59, 80, 141, -24, 20, 139, 52,
  67, 6, -45, -90, -7, 60, 58, 57, -29, -5, -73, -66, 54, -89, -31, 93, 27,
  -75, -3, 101, 35, -85, -70, 2, 76, 51, 8, -38, 72, -14, -47, -183, -4,
  -130, 58, 32, 111, -29, -96, 74, 11, 50, -35, -92, -1, 70, 34, 73, 75,
  -41, -53, -8, -17, -149, -146, -13, 1, -47, -25, -145, 26, -36, 41, -60,
  62, -7, 40, -11, -81, 67, 0, 106, 13, -43, 13, 6, 145, 111, 14, -1, -1,
  -58, 106, 62, 6, 12, 44, 102, 7, -11, 21, 62, -38, -14, -59, -92, 19, 60,
  84, 42, -55, 55, 74, 71, -58, -17, 12, -74, 50, -102, -29, 29, -40, -7,
  -44, -56, -29, -162, 16]

theorem fractionalNearFrameSubtreeG1R0135_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0135Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0135Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0135Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0135_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0135LowerBoundTable : List ℤ :=
  [-65, 3, 2, -18, 1, 2, 1, 1, 132, 178, -20, 298, 8, -17, -266, 78, 232,
  -239, 31, 174, 321, -152, -176, 56, -55]

def fractionalNearFrameSubtreeG1R0135LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0135Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0135LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
