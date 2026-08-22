import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0107`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0107Mask : ℕ := 960719530690904

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0107Witness : Array ℤ :=
  #[87, 141, 15, -26, -234, 84, 49, 48, 34, -18, 13, 74, -138, -86, 127, 9,
  128, 182, -40, -53, 66, 131, -150, 17, -83, -13, 26, -140, -30, 19, 57,
  -108, 88, 151, -224, -141, 203, 105, 50, -110, -217, -17, 67, -185, -197,
  -240, 66, -9, 190, 120, 38, -62, -133, 160, 157, 12, -20, -47, -45, 49,
  -65, 74, 13, -168, -58, 0, 94, 68, 137, 2, -72, -178, -47, 179, -86, 98,
  -123, -3, 179, 235, -194, 81, 55, 112, -214, 89, -62, 207, -6, 67, 172,
  -46, -144, 46, -234, 93, -190, 284, 153, 128, 90, 48, -61, 167, -20, 39,
  -45, -74, -119, -58, 78, -43, 47, 173, -14, 0, -143, -75, -4, -135, -33,
  -3, -101, 40, 47, -86, 52, -20, -34, 52, -110, 74, 9, -83, 13, 50, 83, 36,
  89, 161, -192, -51, -93, -35, 102, 83, -194, -5, 70, 15, -158, -49, -93,
  1, 152, 90, 64, -14, -79, 66, 114, 51, -79, 172, 135, -42, -82, 158]

theorem fractionalNearFrameSubtreeG1R0107_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0107Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0107Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0107Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0107_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0107LowerBoundTable : List ℤ :=
  [-154, -21, -56, 1, 72, -67, 171, 2, 181, -87, 8, -153, 403, 12, 138, -83,
  -17, 462, 776, 251, -131, 268, 210, 10, 368]

def fractionalNearFrameSubtreeG1R0107LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0107Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0107LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
