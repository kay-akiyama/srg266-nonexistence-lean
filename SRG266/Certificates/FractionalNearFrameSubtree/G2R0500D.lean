import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0500`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0500Mask : ℕ := 5811383568942168

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0500Witness : Array ℤ :=
  #[92, -97, -171, 82, -61, 246, 100, -93, 88, -132, 149, 135, -221, 57,
  121, 54, 144, 250, 90, 145, -215, 55, 63, -58, -174, -113, 130, -145, 107,
  58, 50, -19, -185, -28, 31, -236, -108, 33, 32, 162, -58, -193, -163, -14,
  -165, -104, -46, 167, 165, 240, -159, 266, -207, 93, 80, 129, -31, 256,
  16, -156, -52, -162, -62, 20, 51, 175, 115, 165, -83, -44, 100, -9, -175,
  -58, 9, 9, 138, 134, -152, -71, -30, -117, -153, 173, 245, 128, 78, 144,
  -65, -91, -163, 29, 129, 101, 88, -57, 32, 142, -95, 97, -115, 356, -38,
  240, 81, 111, 75, -311, -5, -156, -393, 87, -322, 42, -38, 42, -59, 51,
  -86, 167, 42, -130, -354, 0, -108, 94, 155, 161, 144, 17, -104, -62, -18,
  -36, -111, -93, 22, 63, 36, 284, 52, 57, 144, 56, -129, 90, 274, 116, 117,
  -93, 128, -75, 208, 217, 294, 87, -149, 67, -292, -48, -178, 81, 34, 203,
  157, -139, 153, -16]

theorem fractionalNearFrameSubtreeG2R0500_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0500Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0500Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0500Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0500_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0500LowerBoundTable : List ℤ :=
  [-40, 216, 72, 295, 146, 3, 177, 44, 2, 340, 22, 314, -191, -642, 447, 45,
  171, 604, 347, 383, 553, 599, 759, 281, 470]

def fractionalNearFrameSubtreeG2R0500LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0500Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0500LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
