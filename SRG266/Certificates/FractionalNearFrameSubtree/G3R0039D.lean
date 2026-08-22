import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0039`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0039Mask : ℕ := 954165718783122

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0039Witness : Array ℤ :=
  #[38, 32, 26, 46, 15, 29, -22, -29, -32, -21, -29, 3, 15, -4, 0, -31, 24,
  22, -52, -29, -20, 14, 24, 44, 23, -34, 26, 15, 9, -34, 8, -4, 1, 25, 39,
  -11, -30, 22, -17, -16, -34, -3, 15, -6, -10, 25, 15, -40, -35, -3, 43, 7,
  -9, -42, -5, -13, 25, 0, 18, -45, 50, 10, 49, 18, 28, -2, -9, -1, 24, -17,
  36, 11, 53, -8, -1, -15, 6, 35, 32, 28, -22, -15, -13, -17, 17, -37, 16,
  -45, -16, 42, 8, 30, -8, 27, -16, 9, -10, -48, 21, 41, -9, -25, 0, -48,
  -17, -11, -29, 16, 7, 27, 11, -10, -4, 8, 15, -12, 12, -22, 15, 4, 10,
  -22, 46, 34, 8, -15, -15, -28, -22, -4, 44, -29, -9, -9, -19, 31, -5, -9,
  38, 10, 51, -40, 42, -22, 31, 20, 29, 46, -17, 17, 1, 26, -8, -28, -16,
  -24, -25, 39, 39, 20, 40, 28, -7, -6, 33, -28, 32, 10]

theorem fractionalNearFrameSubtreeG3R0039_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0039Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0039Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0039Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0039_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0039LowerBoundTable : List ℤ :=
  [-1, 80, 74, 40, 30, 3, 3, 21, 43, 39, -61, 9, 84, 58, 35, 138, 76, 77,
  -8, 187, 62, 12, 10, 135, 68]

def fractionalNearFrameSubtreeG3R0039LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0039Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0039LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
