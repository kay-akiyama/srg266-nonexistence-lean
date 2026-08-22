import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0082`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0082Mask : ℕ := 899219470010657

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0082Witness : Array ℤ :=
  #[84, 84, 124, 21, 172, -2, -98, -54, 0, -119, -115, -46, -12, -20, -3,
  91, 81, -60, 6, 19, 7, 30, 133, -96, -99, 11, 0, 3, 16, 12, 29, 2, 27, 23,
  -57, -94, 17, 219, 82, 104, -53, -61, -14, -84, 178, 60, 20, -17, 48, -3,
  9, 12, 16, 17, -28, -93, 7, 34, 74, -37, -6, 55, 7, 34, -13, 24, 10, -114,
  -8, 62, 6, 40, 0, 30, -19, 23, -30, -78, -47, 5, 17, -6, -11, -21, -14,
  17, 99, -87, 116, -58, -39, -36, -18, -21, -78, -79, -68, -77, -16, 40,
  48, -10, 28, -4, -18, -7, 102, -11, 81, -29, 30, 46, 26, 118, 72, 79, -99,
  -123, 60, 60, 7, 89, 98, 36, 29, -24, 18, 61, 44, -14, 79, 24, -26, 0, -2,
  -32, 5, 7, 11, 17, 32, 131, 30, 76, 29, 60, 48, 27, 7, 44, -15, 25, -18,
  -29, -33, 38, 40, 58, -3, -69, -6, -20, 0, -5, 2, 0, 110, -102]

theorem fractionalNearFrameSubtreeG1R0082_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0082Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0082Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0082Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0082_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0082LowerBoundTable : List ℤ :=
  [90, 217, 3, 79, 2, 185, 13, 232, 234, 246, 168, 188, 396, 46, -16, -2,
  56, 3, 155, 1, 91, 10, 310, 185, -33]

def fractionalNearFrameSubtreeG1R0082LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0082Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0082LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
