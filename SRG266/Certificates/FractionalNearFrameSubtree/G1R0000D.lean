import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0000`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0000Mask : ℕ := 236306694982149

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0000Witness : Array ℤ :=
  #[-13, -79, 31, -263, -113, -250, -178, -32, 32, 89, -172, -23, 16, 155,
  246, 292, 199, 196, 106, 149, -94, 76, -182, 6, -47, 120, -71, -78, -84,
  -18, 25, -25, -50, 13, -65, 5, -53, 160, 109, 49, -121, -53, -271, -132,
  41, -151, -56, -88, 29, 48, 39, -4, 60, 91, 111, 30, 89, 14, -78, -66,
  -57, -140, 67, -17, 156, 110, -60, -55, 74, 158, -62, -31, 105, -39, -7,
  -31, 1, 143, 25, -37, -28, 264, 24, -99, 89, 114, 62, 113, -15, -89, -127,
  39, -127, 200, -19, 137, 19, -77, -37, -90, -158, -18, 121, -95, 177, 148,
  109, -176, -58, 85, -27, -88, -91, 154, -101, 170, 28, 126, 105, 21, -94,
  -17, 12, 71, -28, 106, 71, 26, -108, -83, 157, -17, 6, 17, -35, 79, 81,
  -66, -67, -110, 46, 6, 247, -7, -152, 153, 95, -53, -34, -3, -155, 23,
  107, 22, 0, -266, -124, -167, -17, -73, 27, -101, -27, 37, 108, 98, -1,
  -82]

theorem fractionalNearFrameSubtreeG1R0000_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0000Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0000Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0000Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0000_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0000LowerBoundTable : List ℤ :=
  [-144, 4, 3, -184, -159, 2, 67, 288, 71, 624, -25, -91, -39, 572, 158,
  297, 155, 14, -209, 129, -92, 91, 402, 11, -79]

def fractionalNearFrameSubtreeG1R0000LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0000Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0000LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
