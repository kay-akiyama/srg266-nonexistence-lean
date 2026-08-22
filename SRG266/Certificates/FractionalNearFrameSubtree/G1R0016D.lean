import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0016`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0016Mask : ℕ := 273460317577353

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0016Witness : Array ℤ :=
  #[-96, 16, -115, 0, -14, 171, -102, 0, -75, 12, 0, 175, 71, 55, 73, 64,
  -29, 97, -33, 7, 46, 56, 107, 136, -67, 81, 31, 22, -33, -117, -24, 19,
  -136, -114, -113, -18, -30, 80, 91, 172, -99, -42, 27, -98, 24, -37, 170,
  42, 53, 122, -172, 103, -19, -151, -131, 53, -23, -20, -5, 13, 94, -36,
  -53, 90, 30, 91, -42, 13, -17, 47, 37, 69, -89, -148, -20, -104, 7, 183,
  36, 22, -51, -35, 36, -178, 40, 101, 50, -101, 26, -111, -154, 72, -85,
  115, 45, 207, -70, 75, -138, 8, -183, -18, -63, -7, 124, -54, 36, 127,
  -142, 98, -37, -24, 107, -142, -72, 16, -98, -22, 52, -25, 9, 275, 35, 47,
  -53, -176, 189, 63, 3, 169, 13, 64, 99, 71, -43, -2, 50, -21, 46, 10, 82,
  -70, -75, -57, -74, 0, 13, 27, 117, -61, 37, 64, 118, 30, 97, -69, 4,
  -187, -25, -37, -51, 35, -28, -106, -70, -54, -4, -164]

theorem fractionalNearFrameSubtreeG1R0016_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0016Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0016Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0016Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0016_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0016LowerBoundTable : List ℤ :=
  [-130, -79, -206, 3, 203, 195, 1, 54, -178, 81, 99, 243, 195, 43, -239,
  -219, -236, 230, 154, 219, 227, 782, 119, -37, 17]

def fractionalNearFrameSubtreeG1R0016LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0016Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0016LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
