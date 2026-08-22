import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0015`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0015Mask : ℕ := 1006795401103875

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0015Witness : Array ℤ :=
  #[31, -5, 21, 79, 0, -63, -7, 39, -6, 58, 9, -7, 18, -1, -95, 45, -7, -30,
  28, -6, -82, 15, 27, 10, 54, -7, 3, -9, -7, 0, -12, -56, 12, 4, -38, -12,
  82, 45, -12, -65, -31, 51, 0, 0, 31, -3, 26, 62, 21, -7, 6, 38, -48, -50,
  45, 71, -50, -130, -13, 9, 21, -21, -1, -39, -4, -1, 29, -5, 68, -8, 11,
  -46, 109, -26, 73, -28, -144, -16, 3, -52, 75, -72, -3, -43, 4, -7, -39,
  15, 44, 12, 58, -13, 26, -17, 18, 26, 14, -9, -2, -9, 14, -37, 71, -4, 14,
  33, 34, -57, 37, -35, 4, 19, 80, -11, -35, -27, -53, -5, -24, 16, -17, 17,
  22, -14, -41, -56, 31, 2, 101, 32, -7, -3, -70, 26, 11, -42, 24, 19, -9,
  43, 28, -55, 92, 7, 1, -60, 8, 58, 21, 35, 18, 38, 42, -29, -22, 13, -14,
  45, -55, -6, 40, 28, 12, 26, 136, -46, 36, -58]

theorem fractionalNearFrameSubtreeG5R0015_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0015Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0015Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0015Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0015_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0015LowerBoundTable : List ℤ :=
  [-6, 107, 61, 2, 2, -12, 12, 19, 26, 104, 167, 11, 164, 95, -72, 168, 123,
  5, 88, 8, 181, 85, 10, 10, 9]

def fractionalNearFrameSubtreeG5R0015LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0015Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0015LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
