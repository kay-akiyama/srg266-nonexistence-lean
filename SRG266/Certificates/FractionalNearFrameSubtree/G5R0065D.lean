import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0065`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0065Mask : ℕ := 5015757607604998

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0065Witness : Array ℤ :=
  #[94, 87, -4, 22, 78, -30, 16, 96, 13, -4, 56, -128, -31, -42, -9, 0, -19,
  0, -101, -58, -49, -40, 35, -60, 32, -63, -15, 30, 149, 68, 25, 114, -49,
  37, 24, 14, 51, 34, -101, -19, 13, 78, -155, -76, 0, 121, 50, -1, 69, 14,
  -71, -168, -15, 99, -46, 89, -33, -75, -28, -59, -97, 87, 23, -38, -44,
  -16, 21, 122, -11, 28, 93, -2, -5, 51, -13, -34, 53, 16, 13, 9, -1, 15,
  37, 69, 55, 32, 22, -11, -105, -88, -33, 61, -68, -10, 55, 28, -98, 21,
  -19, 37, -76, -61, 64, 71, 108, 68, 84, 47, 33, 21, -40, 39, -37, 44, 38,
  -10, 48, -35, 0, -111, -74, 76, -14, 61, 44, -72, -59, -41, -18, 40, 38,
  -94, -49, 37, 97, 125, 106, 61, -2, 28, 13, 125, 84, 129, -6, -11, 38, 1,
  24, 0, -45, 97, 23, 20, -48, 78, 10, -13, 24, -116, -87, -68, -20, 3, -57,
  -105, -57, -40]

theorem fractionalNearFrameSubtreeG5R0065_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0065Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0065Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0065Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0065_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0065LowerBoundTable : List ℤ :=
  [-32, -13, -47, 109, -6, 70, 164, 5, 2, 352, -9, -110, 295, 148, 111, 233,
  31, 18, 297, 189, -163, 10, 312, 354, 74]

def fractionalNearFrameSubtreeG5R0065LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0065Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0065LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
