import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0147`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0147Mask : ℕ := 1376191057428682

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0147Witness : Array ℤ :=
  #[20, 49, 31, -86, -78, -3, -25, 0, 30, -2, 27, -13, -4, 45, 38, 59, 20,
  82, 51, 1, 55, -33, 9, -66, -27, 0, 25, -5, 23, 38, 19, 41, -81, -43, -37,
  -26, -26, 44, 30, 43, 39, -6, 33, 90, 30, -41, -35, 29, 38, 57, -34, 2,
  75, 60, -4, 18, 8, -62, 110, 54, -4, 12, 24, 9, 59, 46, -30, -38, -2, 16,
  49, 68, 72, 73, 56, 75, -32, 53, 26, 84, 53, 52, 47, 14, 25, -30, 49, 47,
  47, 53, 14, 15, 113, 71, 61, 56, 40, 44, 0, 42, 39, 18, 35, -4, 30, 7, -3,
  8, 10, 6, -31, -38, -19, -33, -21, 20, 71, 29, 15, 24, -42, -42, -9, -46,
  -29, 32, 19, -25, 64, -2, 74, -25, 27, -13, 3, 22, -36, -24, -7, 70, 19,
  25, 19, 5, 20, 55, -16, -30, -88, -36, 24, -53, -72, -6, -9, -38, -33, 5,
  31, 18, 35, 3, 27, -14, -30, -7, 47, 49]

theorem fractionalNearFrameSubtreeG2R0147_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0147Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0147Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0147Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0147_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0147LowerBoundTable : List ℤ :=
  [142, 3, 228, 173, 212, 73, 249, 192, 81, 50, 105, 43, -169, 416, 428,
  442, 142, 175, 152, 223, 178, 316, 169, 12, 199]

def fractionalNearFrameSubtreeG2R0147LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0147Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0147LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
