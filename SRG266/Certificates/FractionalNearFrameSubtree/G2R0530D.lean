import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0530`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0530Mask : ℕ := 6780389390266913

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0530Witness : Array ℤ :=
  #[88, -96, 57, -80, 53, 99, 0, 103, 145, 63, -17, -44, 0, 74, 73, 2, -10,
  63, 46, 29, 50, -67, 67, 13, -54, 0, -30, 31, -8, -29, 7, 148, 83, 75, 32,
  24, -21, 1, 38, 56, 7, -23, -28, -66, 30, 1, 61, 51, 16, -75, -14, 32, 57,
  -39, 17, -61, -21, -9, -45, 0, 61, 19, 16, 76, 93, 17, 3, 27, 17, 40, -12,
  8, 10, -9, 1, 38, -47, -21, -59, -50, 31, 42, 55, 40, 55, -12, -32, 14,
  19, -28, -14, 49, 9, -37, -4, 0, -65, 25, 72, -39, -12, -22, 12, 46, 24,
  -3, -79, -20, 12, 6, 8, 45, 72, 26, 34, 22, -32, 49, -64, -20, 20, 55, -6,
  3, 81, -1, -13, -34, 25, 41, 16, -13, 4, -36, -57, -18, 48, 89, -27, 34,
  -27, 42, 5, -18, -5, 25, -10, -45, -8, -17, 15, 5, 17, 14, 7, 49, 32, 6,
  -6, 19, -10, -4, -69, 50, -31, 29, -32, -141]

theorem fractionalNearFrameSubtreeG2R0530_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0530Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0530Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0530Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0530_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0530LowerBoundTable : List ℤ :=
  [86, 5, -51, -15, 1, 253, 128, 423, 191, 66, 95, 111, 164, -186, 95, 87,
  298, -90, 144, 95, 163, -68, 274, 183, 439]

def fractionalNearFrameSubtreeG2R0530LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0530Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0530LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
