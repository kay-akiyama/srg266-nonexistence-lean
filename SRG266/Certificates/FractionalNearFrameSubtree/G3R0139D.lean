import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0139`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0139Mask : ℕ := 6846355492178570

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0139Witness : Array ℤ :=
  #[66, 40, 31, 1, 46, 40, -23, 8, -26, -103, -28, 33, 8, 38, -25, 45, 44,
  42, -52, 17, 74, 15, 23, -36, -42, -2, 0, 0, -44, -36, 19, 98, 34, -7,
  -58, -50, -5, -52, -7, -20, -13, -18, -3, 14, 29, -46, 6, 38, -29, -48,
  -29, -43, 36, 54, 8, 33, 58, -79, 36, 2, -14, -24, 22, 42, 43, 118, 22,
  -32, -62, 30, -25, -12, -6, 0, 0, 34, 32, 1, -44, 3, -3, 29, -4, 13, -1,
  12, 39, 10, -37, -78, -30, -31, 88, 32, -9, -43, -21, -27, -34, 12, -2,
  -10, -41, -12, 51, 67, 51, -10, 5, -23, -18, 22, 6, -20, 41, 68, 73, -1,
  15, 22, -29, 18, 43, 37, 41, 27, 39, -108, 70, 0, 5, 0, 30, -20, 9, 49,
  -10, 0, 32, -7, -21, 5, 37, 21, 33, 62, 26, 44, -14, -23, 37, 26, 48, -24,
  3, 23, -11, 18, 48, 4, 0, 25, -30, -21, -11, -116, 25, 15]

theorem fractionalNearFrameSubtreeG3R0139_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0139Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0139Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0139Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0139_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0139LowerBoundTable : List ℤ :=
  [17, 104, 73, 90, 2, 102, 58, 2, 12, 196, 43, 223, 160, -57, 159, 119, 44,
  120, 9, -47, 258, 61, 60, 123, 55]

def fractionalNearFrameSubtreeG3R0139LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0139Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0139LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
