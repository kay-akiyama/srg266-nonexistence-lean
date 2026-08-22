import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0098`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0098Mask : ℕ := 946443034135144

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0098Witness : Array ℤ :=
  #[13, 99, 6, -17, 22, 230, 15, 1, 126, -78, -10, -2, -128, -76, 0, -42,
  39, -7, -74, 18, -58, -91, -19, 29, 86, -10, -24, 165, 0, -39, 10, 160,
  -79, 44, 124, 57, 153, -32, 81, -4, -56, 0, 45, 104, -46, -25, 5, -69,
  -38, 94, -13, 15, 47, -42, -31, 134, -51, 210, 56, -20, 34, 2, -31, 103,
  -46, 21, 46, 50, -46, 71, 5, -66, 10, -29, -160, 10, 17, 79, 69, 102, 13,
  64, 54, 61, -17, 127, 2, 74, -34, 89, 0, 73, 15, 19, 100, -76, -31, 27,
  30, 16, -111, -38, -23, 50, -16, 42, 56, -25, -67, -62, -30, 67, 29, -36,
  -136, -38, -43, -102, -41, -14, 128, 2, 98, -17, 106, -108, 131, 105, 5,
  84, 37, -98, -16, 65, 34, -90, -4, -13, -14, -5, 78, -4, -116, 31, 9, 31,
  18, 106, 78, -164, -7, -43, 112, 100, 65, 67, 59, -6, 9, 39, 90, 71, 111,
  45, -20, 63, 51, -11]

theorem fractionalNearFrameSubtreeG1R0098_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0098Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0098Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0098Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0098_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0098LowerBoundTable : List ℤ :=
  [135, 187, 248, 157, 3, 134, 198, 196, 131, 228, 127, 149, 60, 460, 323,
  418, 254, -48, 613, 106, 212, 10, 323, 387, 252]

def fractionalNearFrameSubtreeG1R0098LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0098Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0098LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
