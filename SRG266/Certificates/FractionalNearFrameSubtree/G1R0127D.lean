import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0127`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0127Mask : ℕ := 970608667625840

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0127Witness : Array ℤ :=
  #[47, 0, 1, 1, 14, -61, 21, -42, 36, -44, 57, 62, 45, -41, -1, -2, -70,
  -61, 29, -47, 80, -23, 16, -10, 0, 75, 128, -14, -57, 140, -47, 10, -41,
  63, 75, 23, -102, -169, -156, 19, 16, 134, -2, 101, 6, 10, -24, 27, -13,
  23, -35, -100, -59, 0, -98, -50, 150, 21, -30, 3, 31, 11, 25, 67, 71, -2,
  104, -92, 40, 46, 38, 41, 62, 18, 148, 11, -89, 5, -1, -36, 15, -48, -6,
  -42, -56, -34, -2, 103, 36, 168, -113, -16, 5, -105, -12, -56, -1, 130,
  37, 4, -56, 123, 3, -19, -15, -21, -23, -151, 28, 27, 28, 16, 127, 115,
  95, 74, -16, 17, 69, -25, 63, -73, -73, 73, -41, 23, 93, 11, 27, -5, 83,
  -31, -19, 72, 71, -1, 19, -19, 38, -13, -13, -98, 33, 57, 108, 134, 43, 3,
  36, 74, 49, 78, 20, 12, 24, -32, 7, 87, -77, 20, 40, 48, -35, 30, -55, 88,
  -80, 136]

theorem fractionalNearFrameSubtreeG1R0127_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0127Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0127Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0127Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0127_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0127LowerBoundTable : List ℤ :=
  [88, 261, 2, 59, 248, 70, 141, 54, 211, 197, 349, 314, 218, -127, 17, 179,
  203, 492, -86, 9, 170, 278, 296, 77, 149]

def fractionalNearFrameSubtreeG1R0127LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0127Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0127LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
