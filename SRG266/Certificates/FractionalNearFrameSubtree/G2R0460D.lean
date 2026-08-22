import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0460`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0460Mask : ℕ := 5807292576080522

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0460Witness : Array ℤ :=
  #[59, -17, 65, 137, 52, -1, 0, 46, 50, 118, -35, 4, 53, 34, 1, -94, 23,
  -22, -16, 4, -4, 35, 58, -27, 89, 7, 30, 57, -35, 21, -94, 79, -50, -38,
  132, -49, -29, 46, 127, 30, -15, -52, 32, -11, 30, 83, -41, 99, 97, -72,
  34, 132, -129, -57, 32, -76, -1, 16, 143, 137, 64, 23, 3, 170, 34, -46,
  -34, 17, -108, 84, 14, 10, -52, 23, 68, 24, 25, 94, 86, -56, -17, 53, -96,
  -16, 40, 68, -51, -4, -75, -43, 23, 19, 80, 0, 28, 75, 29, 73, 93, 155,
  18, 63, 58, 20, -103, 94, -49, 59, 16, -25, 23, -69, -27, 79, -91, -23,
  -98, 58, -90, 119, -188, -41, -4, 165, 20, 46, -83, 29, 98, 72, 90, -62,
  -26, 0, 82, 102, -27, -93, -98, -35, 60, 25, -235, 57, 97, 140, -3, 5, 86,
  -18, 69, 84, 46, -62, 50, -27, 177, 108, 50, 45, 87, 51, 35, -73, 86, -27,
  8, 83]

theorem fractionalNearFrameSubtreeG2R0460_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0460Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0460Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0460Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0460_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0460LowerBoundTable : List ℤ :=
  [150, 209, 180, 342, 94, 114, 282, 222, 265, 97, 268, 9, 404, 123, 9, 192,
  471, 10, 354, 573, 697, 275, 281, 285, 161]

def fractionalNearFrameSubtreeG2R0460LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0460Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0460LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
