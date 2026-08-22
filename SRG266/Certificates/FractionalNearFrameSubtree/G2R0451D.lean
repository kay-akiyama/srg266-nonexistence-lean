import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0451`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0451Mask : ℕ := 5793718299907596

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0451Witness : Array ℤ :=
  #[155, 227, 110, 0, 132, -64, 220, 136, -86, 85, -35, -164, 26, -276,
  -135, -106, 22, 224, -34, 127, 165, -83, 99, 0, 50, 58, -58, 219, -32,
  275, -27, -48, 123, 12, 118, -84, 21, 75, -103, 65, 5, 157, 117, -12, -29,
  236, 54, 95, -247, -77, 29, 34, 43, 59, 19, 84, 84, 21, 148, -110, -109,
  -90, 177, -192, 8, -117, -143, 470, 198, -236, 46, 160, 59, 98, 15, -87,
  141, -94, 160, 197, -108, -109, 57, -76, -90, -5, -78, 271, 17, -159, 77,
  -29, -177, -167, 84, -101, 8, -72, 69, 63, -210, 3, 64, -7, -189, -70,
  -49, 74, -1, 134, 213, 200, 94, 162, 4, 75, -59, -16, 22, -22, 211, 249,
  37, -26, -84, 25, -103, -172, -82, 130, -34, 220, 206, -87, 64, 101, 211,
  -234, 77, -96, 10, 18, -157, 19, 10, 119, 27, 150, 2, 9, 87, 19, -2, 13,
  -85, 1, 56, 35, 36, 32, 184, -31, 80, 158, -206, 52, -11, -51]

theorem fractionalNearFrameSubtreeG2R0451_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0451Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0451Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0451Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0451_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0451LowerBoundTable : List ℤ :=
  [155, 230, -8, 1, 363, 577, 1, 410, 151, 296, 530, 600, 185, 164, -32,
  -54, -106, 841, 733, 19, 349, 10, 917, 445, 1269]

def fractionalNearFrameSubtreeG2R0451LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0451Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0451LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
