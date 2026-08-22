import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0073`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0073Mask : ℕ := 5331073158054226

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0073Witness : Array ℤ :=
  #[18, -24, -21, -50, 1, -17, 7, 20, 24, 0, 18, 1, -4, 5, -9, 34, -7, 10,
  -18, -35, 6, -6, -6, -1, 0, 2, 8, 10, 29, 21, -32, -35, -5, -7, -24, 21,
  27, 0, -4, 11, 3, 4, 28, 10, 0, -7, 39, 1, 25, -4, -5, -13, -6, 8, 4, -62,
  8, -19, 32, 4, 0, 25, 20, 19, -9, -51, 0, 26, 2, -12, -1, 12, 29, -28,
  -28, 39, -45, -45, 26, 20, 24, 21, -10, 7, -14, -7, -10, 10, 1, -14, 5,
  -12, 23, -2, -29, -2, 23, -8, 12, 4, 11, 18, 25, 42, -38, -38, -25, -16,
  -9, -14, 2, -32, 15, 0, -5, 0, 4, 11, -1, -3, -7, 19, 11, 5, -16, -4, -7,
  0, 25, -1, 52, 33, -9, -25, -25, 39, 41, 25, -14, -16, 14, 13, 98, -20, 4,
  -6, -11, -42, -17, -50, -10, -30, 22, 60, 31, 1, 7, 4, -41, 13, 10, 41,
  16, -3, 26, 20, 21, 24]

theorem fractionalNearFrameSubtreeG5R0073_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0073Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0073Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0073Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0073_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0073LowerBoundTable : List ℤ :=
  [9, 36, 29, 33, 21, 129, 2, 2, 2, 84, 15, -42, 9, 19, 158, 76, -162, 32,
  -29, 64, -14, 101, -3, 17, 27]

def fractionalNearFrameSubtreeG5R0073LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0073Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0073LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
