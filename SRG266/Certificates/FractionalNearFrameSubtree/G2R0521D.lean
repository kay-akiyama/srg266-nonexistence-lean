import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0521`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0521Mask : ℕ := 6764088916548625

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0521Witness : Array ℤ :=
  #[2, -14, 5, -43, 45, -66, 27, -28, 59, 0, -16, -1, 43, 52, 132, 23, 23,
  138, 27, 17, 14, 18, 35, 56, -11, 13, -36, -26, 4, 2, -65, -8, -50, -66,
  -104, 23, 83, 5, -27, -63, 25, 148, -4, 82, 41, 60, -36, -3, 25, 48, -43,
  -28, 37, -28, -14, 38, 40, -18, -24, -37, 9, -10, -36, 19, -5, 36, -21,
  46, -26, -73, -4, -23, 48, 4, 55, -12, 5, 9, -24, 14, 17, 11, 2, 12, 13,
  6, -4, -57, 64, 78, -113, -48, 38, -42, 9, -25, -92, 80, -11, 9, 0, -51,
  75, 9, 78, -52, 40, 16, 9, 6, -47, -30, 23, -16, 20, 44, 0, 42, 48, 14,
  -54, -75, 0, -14, -33, 6, 27, -1, -43, -15, -7, 40, 42, 30, 0, -19, -27,
  10, -9, 35, 23, 6, -13, 28, 12, 5, 39, 34, -24, 33, 3, 50, -2, -32, 29,
  34, 50, 42, -24, 4, 67, -21, -29, 4, -24, -69, -33, -42]

theorem fractionalNearFrameSubtreeG2R0521_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0521Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0521Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0521Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0521_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0521LowerBoundTable : List ℤ :=
  [13, 37, -57, -35, 39, 53, 194, 287, 2, 11, -45, 61, 33, 62, 128, 98, 10,
  -5, -101, 185, 55, 94, 61, 240, 11]

def fractionalNearFrameSubtreeG2R0521LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0521Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0521LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
