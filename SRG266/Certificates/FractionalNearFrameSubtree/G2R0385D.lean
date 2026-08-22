import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0385`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0385Mask : ℕ := 5739206256316824

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0385Witness : Array ℤ :=
  #[49, -19, -49, -26, -45, 49, 20, -28, 11, 8, 155, 46, -22, -8, 50, -20,
  -41, 16, 15, 58, 33, 11, 9, 15, -5, -36, -39, -21, 34, -31, 2, -60, -14,
  98, 37, -88, -64, -24, -16, -12, 7, 10, 40, -26, -2, 14, -49, -36, -40,
  -14, 18, -28, 98, -58, -75, -29, -10, -26, 13, 23, 7, 13, 12, -17, 3, 127,
  -3, 18, 109, -9, 17, 36, -16, -2, 39, -77, -24, 73, -1, 3, -2, 15, 10,
  -19, 17, -9, 45, 19, -11, 15, -8, -37, 6, -4, 4, 10, 25, 70, -2, 9, 48,
  -11, -43, -3, 30, -58, -4, 8, -133, -36, -54, 14, 61, -45, -8, -20, -4,
  -92, -12, -8, -47, -57, -20, -2, 22, 56, 7, 71, 63, 0, 18, -41, 50, -36,
  39, 37, 1, 14, 14, -17, 63, -29, 35, 3, 10, 39, -18, -2, 87, 19, 13, 8,
  -6, 62, 6, -98, -52, 21, 23, -97, 3, -29, -36, -20, -10, -3, 26, 1]

theorem fractionalNearFrameSubtreeG2R0385_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0385Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0385Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0385Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0385_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0385LowerBoundTable : List ℤ :=
  [-57, 3, -90, 132, -55, -67, 38, 59, 14, 50, 207, -217, -138, -87, 56,
  -52, 10, 27, 37, 28, 104, 89, 239, 295, 113]

def fractionalNearFrameSubtreeG2R0385LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0385Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0385LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
