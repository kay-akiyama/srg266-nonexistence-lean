import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0058`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0058Mask : ℕ := 4957064161500177

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0058Witness : Array ℤ :=
  #[45, 37, -72, -28, -9, -32, 88, 111, -56, -1, 71, -108, 3, 1, -141, 15,
  36, 48, -2, -34, -43, -29, 88, 21, -40, -72, 108, -22, 4, 0, -4, 60, 12,
  14, 52, -53, -12, -17, 2, -70, -13, -65, 21, 35, -63, 42, -9, 6, 76, 1,
  56, 19, -32, 41, 4, -3, 29, -31, 24, 0, -5, -54, -14, -24, 49, -13, -10,
  2, -76, 22, 61, 51, 37, -60, 17, 73, 0, 14, -3, -17, -7, 68, 46, 49, 19,
  20, -31, 2, -1, -2, 30, 89, -49, 11, -38, 23, 41, 0, 47, 49, 13, 54, 17,
  -42, -66, -20, 79, -47, -1, 66, -23, 130, 75, 34, 137, -175, -49, -130,
  -70, 29, -23, 20, 35, -3, 36, 42, -80, -37, 5, 84, 5, -134, 33, -25, 44,
  66, 7, 59, -37, 18, 0, 61, -39, 44, 55, -28, -11, -41, -14, 29, -50, 17,
  -65, -70, 35, 15, 64, -21, 40, -66, 69, 39, 75, 70, 38, 36, 37, 67]

theorem fractionalNearFrameSubtreeG5R0058_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0058Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0058Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0058Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0058_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0058LowerBoundTable : List ℤ :=
  [30, 71, 173, 27, 1, 22, 132, 63, 1, 152, -10, 9, 159, 214, 132, 140, 290,
  67, 174, 11, -90, -92, 164, 164, 284]

def fractionalNearFrameSubtreeG5R0058LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0058Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0058LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
