import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0127`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0127Mask : ℕ := 5862995728385286

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0127Witness : Array ℤ :=
  #[70, -12, -18, 22, 29, -48, -16, -11, 0, 10, 11, 52, 53, 47, 20, 3, 53,
  81, 81, 64, 55, -37, 50, 22, 26, -8, -9, -4, -57, 0, -22, -26, -21, -6,
  -10, 78, 45, -48, 7, -22, 7, -33, -54, -40, 25, 2, 29, 13, -38, -23, 36,
  58, 26, -4, 0, 5, -18, -18, -23, 12, 44, 60, 21, -3, 8, -28, 69, -54, 45,
  34, -22, 70, 47, 33, 36, 7, 68, -14, -5, -18, -34, 111, 44, 85, 30, 21,
  -27, 32, 70, -7, -46, 15, 19, -3, -30, -17, -111, 17, 31, 0, 33, 6, 23,
  -86, 50, -2, 86, -66, 3, -36, 13, 80, 40, -4, 25, 25, -52, -16, -42, -26,
  0, 29, -12, -9, -51, 26, -24, -76, 41, -8, -3, -46, -2, -51, 70, 13, 52,
  86, -48, 37, 84, 62, -11, 28, -4, 7, 82, 0, -78, 52, 8, 15, 60, 18, -2,
  -1, 20, -20, -25, 29, -1, -9, 161, -41, 48, 19, -16, 8]

theorem fractionalNearFrameSubtreeG5R0127_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0127Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0127Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0127Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0127_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0127LowerBoundTable : List ℤ :=
  [77, 111, 46, 148, 61, 2, 161, 238, 113, -9, 70, 236, 45, 92, -27, 214, 3,
  154, 397, 225, 152, 239, 94, 151, 207]

def fractionalNearFrameSubtreeG5R0127LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0127Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0127LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
