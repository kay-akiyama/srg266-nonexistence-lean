import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0273`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0273Mask : ℕ := 5371512277292556

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0273Witness : Array ℤ :=
  #[36, 36, -3, 51, 83, 3, 25, -2, 30, 83, 65, -44, -54, -19, -4, -1, 30,
  -11, -4, -42, 17, 36, 47, 26, -22, 17, -28, 81, 10, -59, 41, 20, 39, 21,
  -37, -5, 43, -56, -75, -37, 25, -4, 7, -1, 70, 39, -24, 29, 34, -16, 35,
  -5, 3, -46, 61, 37, -45, -54, -50, -54, -20, 44, 27, 1, 0, 35, 62, 23, 35,
  -121, -31, 2, 38, -9, -23, -37, 41, -76, -52, -89, 55, 38, 25, 58, -16,
  -37, -49, 3, 67, 20, 20, 8, 63, 8, 23, -67, -55, -12, 1, -29, -33, 9, -8,
  30, 48, -13, -43, -20, 21, 21, -76, -6, 5, 84, 17, -60, -58, -15, 13, 3,
  52, 8, -31, 12, 0, -2, 41, -67, 34, -42, -28, 61, 38, -87, 98, -9, 82, 18,
  24, -1, 75, 104, 87, -100, -13, -79, 4, 16, -2, -27, 13, 34, 46, -90, 53,
  -45, -61, -108, 19, 20, 19, 70, 54, -19, -56, -90, -22, 66]

theorem fractionalNearFrameSubtreeG2R0273_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0273Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0273Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0273Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0273_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0273LowerBoundTable : List ℤ :=
  [-7, 7, 37, -50, 39, 10, 145, 78, -19, -182, 74, 157, 49, -45, 89, 134,
  170, 74, 11, -128, 246, 9, -121, 100, 194]

def fractionalNearFrameSubtreeG2R0273LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0273Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0273LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
