import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0516`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0516Mask : ℕ := 5812742045731440

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0516Witness : Array ℤ :=
  #[-34, 40, 38, 136, 105, -173, -28, -68, 29, -149, 32, 69, 93, 15, 0, 85,
  21, 42, 124, -128, -3, -50, 20, -152, -11, 63, 149, -62, 122, -46, 34,
  -56, 105, 119, -76, -158, -172, 178, -3, 75, -98, -139, 29, 47, 127, 93,
  -59, -157, 3, 110, -14, 18, -135, 121, 40, 30, -35, 0, 135, -30, -54, -48,
  30, 40, -161, -57, -33, -196, -35, -86, -119, -68, -44, 66, -141, 55, 214,
  84, -75, 99, 155, -121, -104, 112, 59, -169, -90, -191, -193, -62, -48,
  143, -87, 25, 46, 87, 26, -160, -156, 68, -26, 143, -109, -2, 73, 185, 52,
  94, 13, -56, -177, 211, 87, -12, -15, -95, 272, 202, 0, 23, -6, -77, -103,
  82, 34, -93, 5, 85, -7, -34, -83, -73, 83, -116, -90, 92, -34, -114, 138,
  39, -130, -142, 113, -35, 113, -24, 106, -28, 30, 38, 71, -5, 34, 124,
  -71, 19, -31, 15, 38, -16, -92, 61, 25, 14, -18, -4, -93, 156]

theorem fractionalNearFrameSubtreeG2R0516_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0516Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0516Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0516Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0516_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0516LowerBoundTable : List ℤ :=
  [-88, -1, 2, 1, 124, 2, 4, -10, -36, -42, -217, 466, 379, 351, 383, -192,
  -8, 332, 76, -159, -100, 106, -468, -79, -367]

def fractionalNearFrameSubtreeG2R0516LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0516Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0516LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
