import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0129`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0129Mask : ℕ := 970615109880176

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0129Witness : Array ℤ :=
  #[12, 49, -10, 45, -5, -31, 3, -34, -20, 3, -28, 41, 21, -69, 57, 29, 62,
  35, -22, -59, 1, -24, -21, -11, 10, -25, 17, 6, 6, 13, -14, 47, -64, -10,
  10, 88, -35, -12, -96, 5, 69, 65, -6, -13, -29, 39, -37, -35, 41, 18, 30,
  -46, -44, -24, -23, 51, 0, 0, 67, -14, -50, 27, 36, -106, 50, -23, 80,
  -43, -27, -20, -76, -34, -6, -30, -38, 33, -1, 22, 3, -18, 31, -59, -25,
  15, 33, 4, -3, 49, 25, -10, -17, 40, 4, -46, -6, -21, 12, 38, -61, -38,
  42, 70, -59, 40, -12, -43, -64, 3, -9, -48, 34, -6, 80, -3, 1, -12, 42,
  -6, 3, 84, -29, -59, -11, -14, 25, 0, 55, 47, -10, 17, -32, -28, 28, -23,
  37, 7, 53, -13, 1, -26, 11, 1, -10, 38, -5, -42, -44, -1, 67, -2, -22,
  -11, 43, 44, 19, 14, -23, 29, 31, -61, -82, -9, -18, -26, 18, 52, -71, 56]

theorem fractionalNearFrameSubtreeG1R0129_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0129Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0129Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0129Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0129_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0129LowerBoundTable : List ℤ :=
  [-47, 6, -8, -36, 2, 9, 39, 59, -33, 10, 10, -86, 21, 108, 10, -24, -114,
  11, 44, 149, -51, -72, -22, 147, 54]

def fractionalNearFrameSubtreeG1R0129LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0129Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0129LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
