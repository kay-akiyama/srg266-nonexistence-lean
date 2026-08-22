import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0289`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0289Mask : ℕ := 5385222918705554

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0289Witness : Array ℤ :=
  #[-3, -17, 16, -83, -7, -92, -46, 45, 44, -52, -40, -28, 66, 153, 184, 18,
  33, 48, -62, -40, 26, 102, -7, 84, 40, 17, 44, -77, 0, -63, 20, 52, -18,
  45, -50, -14, 58, 2, -9, 86, -37, -6, 71, -24, 6, -14, -118, -6, 62, 6,
  48, -10, -82, 17, -6, 59, 34, -69, -146, 26, 68, 56, -20, -57, 53, 118,
  141, 55, 59, -32, 35, -27, 26, 56, -76, 71, -14, 79, 8, 27, 93, 53, -15,
  63, 67, 44, 70, 32, 10, -86, 42, -24, 40, 36, -115, 33, 47, -25, 100, 5,
  -2, 46, 87, 78, -38, 81, 64, 41, 86, 49, 2, 177, -6, -41, -74, 35, 11, 39,
  17, 7, 2, -142, -77, -20, -36, -51, 13, 55, 85, 41, 0, 52, 4, -38, 15, 84,
  -83, -22, -49, 36, 21, -9, 31, -3, 46, 0, -46, 105, -7, -133, 39, 26, 193,
  -41, -36, -65, 72, 46, -86, 22, 0, -22, 69, -73, -35, -50, 105, 25]

theorem fractionalNearFrameSubtreeG2R0289_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0289Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0289Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0289Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0289_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0289LowerBoundTable : List ℤ :=
  [96, 45, 243, 176, 210, 2, 234, 35, 89, -51, 518, -147, 182, 251, 212,
  127, 189, 216, 230, 165, 74, 297, 274, 585, 10]

def fractionalNearFrameSubtreeG2R0289LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0289Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0289LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
