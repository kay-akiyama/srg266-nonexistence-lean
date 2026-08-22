import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0054`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0054Mask : ℕ := 688113640229129

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0054Witness : Array ℤ :=
  #[-112, -139, -92, -100, -69, -92, 75, 35, 90, 62, 17, 87, 40, 69, 31, 81,
  63, 42, 2, -15, -15, 24, -10, 54, 26, 15, 8, -13, -13, -18, -27, -38, -10,
  -16, -16, 27, -6, 56, -27, -25, 17, 24, 26, 19, -31, -42, 14, 14, 41, -12,
  1, -12, -25, 21, -15, -10, 20, -9, 2, 15, -2, -11, -4, 14, 9, 8, -6, 17,
  105, 25, -1, -10, 10, 21, -2, 21, 3, 23, 53, -6, -13, -9, -41, 4, -15,
  -10, -23, -26, 17, 105, -35, -11, 1, -15, -30, -10, -6, 5, 23, 105, -2,
  -2, -3, -6, -11, 7, 7, 4, 17, -96, 10, -127, 31, -109, -97, 3, 3, 127, 11,
  -30, 12, 7, -10, -9, -40, -3, -4, 4, -5, 8, -4, -19, 0, 10, -10, -34, 3,
  8, 15, 6, 63, 8, 2, 25, 26, 33, 31, 41, 55, -4, 6, -8, -4, -21, -16, -23,
  -17, -1, -6, -43, -2, -10, -6, -8, -34, 2, -12, 31]

theorem fractionalNearFrameSubtreeG1R0054_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0054Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0054Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0054Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0054_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0054LowerBoundTable : List ℤ :=
  [-8, 1, -14, -28, 111, 33, 2, 1, 64, 23, 98, 11, -60, 10, -3, -32, -22,
  -54, -10, -51, 9, 205, 55, 186, -107]

def fractionalNearFrameSubtreeG1R0054LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0054Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0054LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
