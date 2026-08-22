import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0646`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0646Mask : ℕ := 36107853241766409

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0646Witness : Array ℤ :=
  #[12, 19, 16, 16, 7, 153, -76, -52, -40, -43, -74, -81, 2, 26, 30, 13, 25,
  50, 7, -8, 4, -12, 104, 21, -19, -14, -18, -1, -17, 6, 43, -84, 13, 7, 7,
  -32, -18, 4, 2, 34, -5, -1, -3, 1, 96, 10, -5, 57, 24, 18, -3, -8, 0, -5,
  -8, -5, -61, 2, -1, 16, 12, -9, 37, 9, -7, 3, -45, 42, 73, -4, 17, 4, 10,
  -21, 9, -7, -48, 10, 22, 30, 3, -11, -11, -24, 75, 10, 13, 19, 8, 44, 17,
  -10, 9, -18, 55, -11, -5, -3, -6, -20, 8, -82, -69, -72, -64, -14, -11,
  -11, -17, -7, 5, -7, -1, -3, 23, -2, 23, 21, 13, -2, 12, -4, -34, 7, -7,
  14, 25, 45, 9, -26, 6, -7, 0, 30, 16, -35, -7, 16, -8, 45, 62, -9, 14, 20,
  25, 55, -10, 28, 3, 13, 52, -1, 18, -96, -1, 18, -43, 22, -14, 6, -51, 1,
  -59, -46, 28, -50, 15, 0]

theorem fractionalNearFrameSubtreeG2R0646_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0646Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0646Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0646Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0646_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0646LowerBoundTable : List ℤ :=
  [-2, 28, 3, 132, 43, -19, 4, 1, 2, -102, 14, 6, 98, 11, 27, -29, -83, 103,
  44, 96, 128, 65, 9, 10, -3]

def fractionalNearFrameSubtreeG2R0646LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0646Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0646LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
