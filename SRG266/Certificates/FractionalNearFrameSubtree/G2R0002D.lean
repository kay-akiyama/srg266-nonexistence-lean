import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0002`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0002Mask : ℕ := 244971650601105

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0002Witness : Array ℤ :=
  #[-69, -43, -54, -77, 48, 32, -19, -22, 65, -16, 29, -15, 89, -96, 28, 9,
  0, -93, 87, -56, -46, -25, -108, -26, -90, -158, -65, 3, 0, 144, 113,
  -151, -13, -33, -85, -26, -34, -17, 176, 103, -61, -88, -126, 8, 222, -74,
  15, 286, -19, -54, -95, 39, -55, -154, -87, 182, -14, -162, 304, -100,
  -35, -102, -24, 20, 42, -197, 143, 34, 32, 85, -45, 46, 8, -118, -24, 94,
  -46, 134, 98, 90, 21, -15, 80, 11, 50, -119, 36, 47, 31, -16, 124, 171,
  -103, -48, 105, 181, -501, 63, -20, 87, -151, -1, -17, -65, 57, 139, -486,
  -88, -165, -81, -260, -151, -64, -183, -146, 71, 398, 50, 103, -30, -18,
  -53, -79, 128, 93, -69, -61, -15, 88, -174, 79, 61, -1, 57, -122, -21, 68,
  -24, -13, -11, 34, -45, -46, -79, 92, 338, 1, -90, 73, -133, 219, 90,
  -303, 69, 5, -16, -13, 75, -30, 252, -31, -57, 121, -50, 203, 187, -258,
  278]

theorem fractionalNearFrameSubtreeG2R0002_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0002Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0002Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0002Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0002_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0002LowerBoundTable : List ℤ :=
  [-247, 218, -141, -343, 154, -69, 25, -153, 46, 253, -173, 28, -340, 147,
  -32, -158, 9, 345, 380, 243, 249, -83, 10, -326, 12]

def fractionalNearFrameSubtreeG2R0002LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0002Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0002LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
