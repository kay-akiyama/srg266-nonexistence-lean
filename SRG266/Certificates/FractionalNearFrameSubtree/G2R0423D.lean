import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0423`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0423Mask : ℕ := 5778664538677836

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0423Witness : Array ℤ :=
  #[-311, -264, -56, 69, -67, -104, -182, 78, 38, 19, 86, -2, 0, -66, 139,
  185, -100, -196, -12, 69, 40, -59, -22, -197, -92, 21, 114, 31, 163, -84,
  -303, -196, -169, -183, 235, 319, 96, 62, 82, 63, 346, -4, -84, -79, -162,
  -83, 76, -50, 101, -41, 65, -8, -35, -153, 377, 183, -122, -61, -71, 0,
  345, 150, 177, -124, -115, 15, 99, -171, -8, -133, -53, 237, 45, 81, 156,
  7, 75, -20, 112, -155, 31, 103, 99, 28, -35, -87, -55, 97, 101, -172, 102,
  -97, 91, -59, 54, -135, 83, 52, 119, 121, -278, 36, 76, 25, -35, -127,
  307, 74, 137, -289, -66, -126, 5, 4, -38, -119, 243, 58, -160, 60, -22,
  75, 59, 204, 63, -239, -250, 0, 61, 128, 26, 124, 55, 44, -57, -102, 19,
  -219, -54, -133, -150, 3, -75, 172, 102, -88, 44, 11, 133, -115, 56, 105,
  -10, 61, 179, -74, -186, 36, -100, 139, 50, -3, 144, 62, 134, 171, -326,
  -77]

theorem fractionalNearFrameSubtreeG2R0423_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0423Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0423Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0423Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0423_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0423LowerBoundTable : List ℤ :=
  [-163, -78, 110, 136, -143, -8, -51, 2, 86, 315, 180, 626, -61, 506, 255,
  -269, 10, 771, 207, 414, -7, -589, -332, 372, -158]

def fractionalNearFrameSubtreeG2R0423LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0423Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0423LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
