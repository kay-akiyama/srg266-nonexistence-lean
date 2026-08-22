import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0034`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0034Mask : ℕ := 870585177053729

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0034Witness : Array ℤ :=
  #[0, -131, 40, 48, -131, -163, -49, -120, 47, 28, -86, -97, 214, -31, 156,
  261, 156, 0, 121, 99, -25, 111, 3, 86, 149, 178, 38, -21, -245, -179, -33,
  -129, 271, 73, 230, -26, 10, -107, 50, -252, -132, 67, 0, -127, 85, 133,
  85, -69, -114, -71, -103, -66, -197, 133, -149, -60, 142, 109, -22, -1,
  19, 13, 21, 87, -135, 123, 30, -22, -31, 9, -23, 36, 105, -77, 6, -110,
  -1, -308, 11, 67, 134, -70, -87, 37, 40, 21, -108, 27, 0, 36, 2, -40, 19,
  98, -93, -81, -269, -29, 13, 99, 26, -71, 70, -131, 107, -182, 1, -11,
  -16, -168, 16, -49, -31, -31, -44, 44, 364, -8, 104, -164, 76, -5, -52,
  71, 127, -15, -83, -203, -45, 176, 366, 21, -66, -37, -54, 158, -263, 12,
  -24, 32, 172, 70, 115, 46, 38, -138, 35, 105, -3, -77, 53, -33, 178, 104,
  197, 159, -170, -165, -99, 318, -20, -262, 44, 26, -115, 12, -310, 154]

theorem fractionalNearFrameSubtreeG2R0034_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0034Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0034Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0034Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0034_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0034LowerBoundTable : List ℤ :=
  [-153, 140, -277, 119, 2, -117, -137, -65, 2, 293, 181, -49, -76, 367, 41,
  271, -50, 75, 406, 422, 11, 82, 541, 11, -240]

def fractionalNearFrameSubtreeG2R0034LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0034Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0034LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
