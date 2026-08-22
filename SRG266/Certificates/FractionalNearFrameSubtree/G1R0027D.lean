import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0027`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0027Mask : ℕ := 468284144791697

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0027Witness : Array ℤ :=
  #[-374, 7, 18, -70, -319, -85, -51, 11, 0, 81, -33, 48, -171, 59, 153,
  145, 0, 220, -19, -129, 0, -158, -208, -198, -96, 22, -75, 103, 139, 62,
  91, 58, -335, 86, -231, 0, 36, -67, 8, 205, -8, 97, 77, -53, 248, 167, 2,
  -384, -193, 118, -21, 186, 258, 140, -30, 4, 147, 236, 117, 133, 3, -125,
  -88, 109, 187, -172, -209, 28, 194, -156, -172, 262, -84, -110, 218, 140,
  27, -121, 225, 22, -128, 468, -40, 54, 17, 162, 93, 27, 80, 210, -36, 224,
  56, 87, 205, 143, 17, -2, 140, 57, -56, 279, 86, 12, 137, -127, 194, -51,
  37, 56, -185, 26, 54, -182, -283, -157, -211, 96, -292, 276, 111, 198,
  201, 52, 79, -45, 1, -165, 43, 11, 80, -102, 65, 73, -80, -40, 101, 42,
  -9, 52, 46, -101, -56, 76, -44, -154, -245, -23, -32, -190, -124, -100,
  -56, 51, 126, 53, 295, 16, 185, 52, 68, 164, 243, 35, 181, 58, -36, -30]

theorem fractionalNearFrameSubtreeG1R0027_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0027Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0027Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0027Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0027_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0027LowerBoundTable : List ℤ :=
  [30, 1, 417, 194, 289, -258, 510, 2, 13, -143, -50, 931, 256, 297, 695,
  -11, 302, 620, 11, 74, 466, 10, 780, 847, 607]

def fractionalNearFrameSubtreeG1R0027LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0027Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0027LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
