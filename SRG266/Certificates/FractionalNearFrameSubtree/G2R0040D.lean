import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0040`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0040Mask : ℕ := 888022878493217

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0040Witness : Array ℤ :=
  #[0, 58, 70, 0, -31, -134, -89, 143, -20, 11, 0, 106, 156, 131, 219, -88,
  76, 36, -30, 319, 235, 166, 68, 35, 82, -166, -75, -98, 73, -88, -179,
  161, 196, 49, 258, -13, -54, -209, -77, -74, 95, 35, 433, 38, -43, 3, 1,
  -90, -132, 46, -90, -320, 95, 80, -191, -57, 190, 38, -3, -176, -148, 48,
  52, -115, 241, -107, -74, 87, -62, -78, -149, 132, -201, -183, 187, 223,
  9, -80, -88, -81, 187, -123, -155, 195, -65, 18, -8, -21, 46, 120, -35,
  62, 201, 130, 11, 49, 6, -19, 50, 226, -168, 104, 15, 89, 46, 120, 20,
  166, 26, 45, 372, 48, -154, -129, 148, 32, 5, -113, 34, 60, 87, 5, -82,
  35, -194, 79, -16, -22, -56, 0, -12, -122, 202, 246, 150, -71, 194, -309,
  -99, 91, -141, 154, 103, 141, -114, -228, -148, 105, -124, 16, -37, 125,
  -110, -82, -86, 201, 0, 41, -99, -61, 268, -294, 74, -5, 110, 65, -124,
  -255]

theorem fractionalNearFrameSubtreeG2R0040_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0040Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0040Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0040Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0040_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0040LowerBoundTable : List ℤ :=
  [-70, -65, 1, -40, 199, 8, 69, 423, 2, 95, -83, 621, 234, 678, 329, 479,
  534, 669, 111, 236, -181, -36, 553, 10, 474]

def fractionalNearFrameSubtreeG2R0040LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0040Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0040LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
