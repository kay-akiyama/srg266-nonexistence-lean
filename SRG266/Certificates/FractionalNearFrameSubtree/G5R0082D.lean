import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0082`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0082Mask : ℕ := 5440781132874502

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0082Witness : Array ℤ :=
  #[-53, 136, 53, -12, 153, 20, 90, 143, 52, 15, 18, -142, -117, -399, -369,
  0, -75, 57, -163, -31, -82, -81, 36, 134, 87, -77, -244, -11, 0, 164, 170,
  142, -17, 182, 260, 19, -104, 245, -23, -212, 161, 155, 27, 70, -65, -163,
  -90, 124, 170, 145, 61, 33, 95, -8, 198, 65, -411, -128, -43, -91, 135,
  -254, 99, 3, -35, 52, -93, -202, -63, 83, 185, -21, -24, 21, 50, -10, -8,
  165, 196, 117, -56, -18, 150, -58, -44, -187, 114, 30, -53, -20, -126,
  -59, 26, 118, 198, 84, 50, 174, -209, -120, 262, -77, -70, 14, 157, -385,
  -163, 135, -43, 92, 55, -11, -163, -360, 140, 119, 153, -28, -68, 61, 268,
  143, -15, 65, 275, 70, -54, 172, -14, -89, -57, -241, -301, 123, 47, -120,
  217, -80, 140, -82, -130, -31, 20, 73, 55, 43, 341, -61, -52, -104, -109,
  132, 100, 388, -96, 231, 139, -348, -374, 50, 154, 20, 101, 151, 176, 112,
  0, 164]

theorem fractionalNearFrameSubtreeG5R0082_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0082Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0082Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0082Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0082_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0082LowerBoundTable : List ℤ :=
  [-117, 259, 2, 2, 429, 155, -198, 3, 121, 728, 10, 100, 452, 207, 10, 507,
  313, 42, -444, 522, 1004, 255, 485, 230, 96]

def fractionalNearFrameSubtreeG5R0082LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0082Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0082LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
