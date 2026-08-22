import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0020`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0020Mask : ℕ := 1047924544606289

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0020Witness : Array ℤ :=
  #[34, 50, -10, 72, 38, 42, -4, -35, -3, 58, 58, -7, 24, -113, -67, 0, -36,
  -75, 40, 52, 48, -5, 43, -19, 7, 48, -32, -10, -35, -73, 103, -1, 41, 33,
  -90, 9, -111, -25, 119, 6, 36, -52, -88, -78, -17, -48, -17, -60, 70, -52,
  5, 0, 39, 71, -42, -10, 32, -34, -55, -19, -78, -84, 49, -25, -11, 23, 66,
  7, -12, 0, 36, 50, 55, 9, 7, 80, -94, 32, 69, -32, -3, -9, -11, 29, 9, 68,
  -71, -12, 45, -5, -62, -63, 10, -24, -52, 5, 17, 25, 99, 34, 11, -19, 46,
  -26, -57, 2, -7, 22, -22, -49, -16, -40, -11, -6, 45, 22, -22, 50, -35,
  24, -11, -22, 23, 63, -69, 51, -34, -33, -60, -49, -39, 47, 30, -30, 67,
  87, 0, 14, 74, 84, 20, 89, 55, -28, 39, 41, 37, 0, -114, -20, 54, -33, 20,
  1, -40, -10, 19, 52, 45, 77, 9, 97, 7, 14, -13, 9, -46, -10]

theorem fractionalNearFrameSubtreeG5R0020_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0020Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0020Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0020Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0020_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0020LowerBoundTable : List ℤ :=
  [-41, 146, 2, 4, 104, -98, 10, 126, 44, 82, 0, 121, 210, -46, 57, 141,
  107, 241, 149, -29, -58, 42, -237, 124, -59]

def fractionalNearFrameSubtreeG5R0020LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0020Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0020LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
