import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0596`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0596Mask : ℕ := 6867778225947732

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0596Witness : Array ℤ :=
  #[-89, 157, -113, -108, 0, 19, 130, -6, 47, -54, -24, 196, 286, 46, 288,
  -115, 180, 149, 239, -21, 320, -90, 375, 54, 229, 135, -252, -306, 337,
  -50, 43, -37, 248, -181, -220, -208, 329, 362, 241, -49, -231, -122, 120,
  62, 312, -114, 399, 258, -55, -56, -26, 234, -131, 225, 43, -299, 305,
  -17, 86, -184, -88, 253, 242, -52, -265, 69, 228, -81, -181, -217, -36,
  -120, 284, -219, 312, 309, -5, 141, 156, 192, 142, -135, -309, 136, 178,
  -62, 270, 165, -130, -95, -18, 187, -50, -119, 363, 34, 189, 113, 413, 71,
  66, 47, -103, -56, 239, 214, 187, 119, -31, 228, 394, 628, -80, -30, 11,
  117, -131, 49, -92, 286, -103, 453, 69, -96, 29, -44, 137, 7, -169, 297,
  168, -220, -103, 277, 138, -179, -31, 46, 413, 73, 52, -271, 163, -95, 0,
  -29, 220, 376, 392, -49, 196, 59, -231, -241, -15, -136, 145, 347, 30,
  108, 96, 221, -10, -327, -115, -15, -279, 196]

theorem fractionalNearFrameSubtreeG2R0596_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0596Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0596Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0596Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0596_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0596LowerBoundTable : List ℤ :=
  [448, 589, 7, 505, 1071, 1358, 228, 656, 718, 1923, -85, 726, 747, 819,
  -270, 713, 428, 1503, 1815, 465, 706, 147, 1081, 812, 659]

def fractionalNearFrameSubtreeG2R0596LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0596Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0596LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
