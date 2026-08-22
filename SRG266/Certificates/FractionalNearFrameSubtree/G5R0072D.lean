import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0072`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0072Mask : ℕ := 5300320653132550

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0072Witness : Array ℤ :=
  #[11, 44, -26, -5, 22, 24, -8, 0, -19, 0, 16, -16, -6, -25, -7, 59, -12,
  0, -71, -19, -33, -4, 19, 6, 57, 9, 19, 14, 48, -48, -39, 0, -31, -5, -6,
  15, 10, -2, -21, 31, 11, 23, -31, 14, -7, 6, 19, 6, -1, -42, -4, -37, 18,
  -13, 11, 3, -26, 7, -51, -32, 29, -32, 68, 22, 30, 1, 58, 22, 10, 16, 39,
  -14, 13, -49, 12, 20, 48, 15, -26, -7, -3, -4, -18, -70, 8, 6, 19, -18,
  -1, -9, 1, -11, -6, 11, 22, 9, 13, 15, -31, 2, 4, -6, 0, 16, 9, 26, 17,
  -18, -15, -14, -17, 8, 16, 20, 65, 23, -15, 0, -9, 33, -25, 28, -6, 6,
  -21, -14, -10, 24, -39, 29, 22, 9, 10, 48, 31, -3, -37, 11, 75, 23, 59,
  50, -42, -26, -114, -8, -35, 29, 41, 13, -13, -41, 2, 8, 59, 0, -8, 8,
  -29, -15, -13, -4, -9, -15, -50, 5, -48, 2]

theorem fractionalNearFrameSubtreeG5R0072_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0072Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0072Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0072Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0072_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0072LowerBoundTable : List ℤ :=
  [-16, -15, 1, 1, -36, 175, -23, 2, 21, 9, 2, 48, 102, 87, 16, 75, -111,
  27, -32, 158, -9, 10, 65, 42, -21]

def fractionalNearFrameSubtreeG5R0072LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0072Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0072LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
