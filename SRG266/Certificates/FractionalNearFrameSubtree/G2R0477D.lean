import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0477`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0477Mask : ℕ := 5809454606639768

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0477Witness : Array ℤ :=
  #[-29, -45, -22, 52, 16, 26, -34, 132, -63, -40, 78, 39, 40, -25, 30, 33,
  15, 33, -40, 58, -24, 129, 58, -68, 1, -41, -38, 17, -41, 8, -31, 15, 21,
  -40, -22, 7, 53, 15, 5, 16, 33, -3, 84, -32, 40, -5, -39, -18, 16, 71, 12,
  -33, -1, 4, -41, -92, 94, 0, 119, 73, 16, 13, 66, -14, 48, 80, -26, 33,
  62, 70, -118, 52, 60, -23, -31, -29, -18, 71, 3, 19, -14, -3, 0, 50, -63,
  75, -92, -30, 20, 53, -38, 8, -88, 15, 17, 10, 112, 80, 54, -58, 95, -2,
  74, -77, 60, -131, -59, 7, -100, 31, 2, 55, 18, 70, -123, -116, 23, -45,
  29, 44, 140, 107, -121, -157, 20, 29, -63, 49, -114, 37, 17, -76, 120, 50,
  -81, 40, 12, 8, 56, 20, 100, 65, 64, 26, 69, 0, 54, 43, -6, 14, 10, 25,
  45, -1, 30, 5, -17, -26, 9, 25, 9, 56, -30, -6, 11, 15, 27, -29]

theorem fractionalNearFrameSubtreeG2R0477_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0477Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0477Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0477Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0477_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0477LowerBoundTable : List ℤ :=
  [80, 82, 47, 172, -24, 109, 66, 1, 192, 141, 82, 10, 176, 222, 64, -25,
  117, 135, 244, 198, 488, 95, 136, 257, 351]

def fractionalNearFrameSubtreeG2R0477LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0477Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0477LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
