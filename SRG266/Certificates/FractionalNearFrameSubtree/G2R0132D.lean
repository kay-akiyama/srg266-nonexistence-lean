import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0132`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0132Mask : ℕ := 1353262231879890

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0132Witness : Array ℤ :=
  #[32, -16, 19, 57, -33, 38, 78, 234, 21, -67, -155, 55, 177, -34, -21,
  129, 45, 151, 62, 105, 38, 86, 60, 115, 54, 143, -51, -164, 0, -257, -44,
  -69, -33, -133, -86, 198, 413, 78, -23, 117, 189, 14, -166, -70, -61, 155,
  -19, 98, 107, 86, -37, -96, -89, -60, -39, -130, 0, 134, 83, -77, 89, 10,
  -1, 99, 16, -133, 229, -83, 2, 1, -66, 143, -86, 78, -187, -80, 31, 111,
  102, 69, -11, -109, -102, -30, 147, -226, -78, -1, 11, -166, 6, 114, 195,
  -63, 162, 113, 129, -57, -44, 71, -10, -86, -71, 24, 60, -237, -5, 75,
  -10, -92, 65, -10, 45, -84, 112, -63, -65, -34, -55, 39, -60, -172, -4,
  38, -26, 193, 156, 80, 144, 93, -3, 59, 19, -122, 32, 24, -39, -95, 50,
  112, -66, 119, -136, 65, -98, 50, 62, -167, -14, -53, -149, 211, -41, -15,
  -5, 40, -189, -97, 171, 70, -114, -1, 91, 6, 330, -28, 52, 100]

theorem fractionalNearFrameSubtreeG2R0132_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0132Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0132Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0132Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0132_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0132LowerBoundTable : List ℤ :=
  [-32, 2, -48, 1, 157, 265, 26, 188, 385, 299, 124, -136, 519, 416, -379,
  -25, -46, 589, 144, 9, 11, 146, 597, 399, 768]

def fractionalNearFrameSubtreeG2R0132LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0132Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0132LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
