import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0088`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0088Mask : ℕ := 5508194746671754

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0088Witness : Array ℤ :=
  #[7, 33, 13, -43, 31, -83, -56, -51, -76, 57, -70, 101, 115, 88, -26, 44,
  74, 31, 68, 172, 53, 6, -107, -42, 12, -66, -27, -24, -63, -36, -28, -62,
  54, -3, -20, 54, 15, -7, 8, 33, 14, -75, -75, -9, -12, 0, 24, 32, 39, 44,
  -43, -14, -17, -1, 0, 8, -39, 44, -36, -51, -4, 74, 27, 8, 18, 38, -11,
  -28, -27, 14, -44, -27, -51, 11, -2, 67, 23, -33, 35, 35, 25, -27, 41, 17,
  -101, -31, -98, 12, -3, -31, 80, -14, 14, -2, 51, -78, 47, 27, -20, 43,
  -34, 24, -89, -14, 34, 25, 14, 66, 71, -17, 3, -31, 63, -6, -19, -80, -64,
  -91, 27, 20, 58, 29, -9, 49, 7, -7, -39, 43, 2, 34, 50, -36, -14, 50, -21,
  27, 0, 50, 38, 9, 51, -17, 24, 8, -13, -15, 61, 3, 31, 64, -13, 47, -5,
  27, -26, -69, -39, -33, 54, 18, -6, 19, 0, 56, 28, 13, -42, 60]

theorem fractionalNearFrameSubtreeG5R0088_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0088Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0088Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0088Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0088_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0088LowerBoundTable : List ℤ :=
  [-14, 73, 2, 94, 1, 51, -9, 43, 36, 249, 305, 18, 14, 181, 157, 9, 70,
  104, -140, 16, -92, 39, -16, 161, 88]

def fractionalNearFrameSubtreeG5R0088LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0088Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0088LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
