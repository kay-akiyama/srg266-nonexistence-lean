import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0037`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0037Mask : ℕ := 954159343635602

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0037Witness : Array ℤ :=
  #[32, 87, 23, 3, 16, 61, 50, -88, 9, -12, -29, -18, 32, -31, -14, -12, 13,
  0, -17, -43, -113, 44, 29, 27, -26, 2, 53, 76, 35, 27, 76, -79, -6, 66,
  16, -12, -57, 56, 8, 55, -35, 0, 75, 18, 41, 23, -46, -96, -36, -47, 61,
  2, 39, -18, 28, 5, 33, 5, -13, -40, 3, 3, 49, -8, -47, -18, 36, 12, -18,
  -9, 7, -42, 31, 28, 12, -9, -64, 53, 21, -19, 65, 62, -34, 6, 12, -15, 38,
  -5, 31, 40, 31, -18, 104, 20, 84, 41, -30, -60, 43, -5, 20, -28, 13, -53,
  0, 6, -42, 9, 30, 1, -25, 6, -26, 10, 28, 12, -16, -40, 44, -40, -5, -22,
  -49, 51, -9, -46, 60, -22, 62, 43, 41, -27, 39, -16, 12, -1, -20, -27, -8,
  10, 85, -62, 13, 6, 42, 38, 22, 23, 42, 30, 23, 32, 11, -76, -22, -35, -8,
  10, 38, 16, -62, 13, -55, -30, -40, -24, -37, 15]

theorem fractionalNearFrameSubtreeG3R0037_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0037Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0037Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0037Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0037_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0037LowerBoundTable : List ℤ :=
  [-15, 8, 89, 76, 1, 53, 85, 68, 72, 29, 10, -5, -168, 116, 110, 273, 288,
  58, 225, 216, -142, 9, -76, 162, 55]

def fractionalNearFrameSubtreeG3R0037LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0037Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0037LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
