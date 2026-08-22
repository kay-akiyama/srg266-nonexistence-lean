import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0126`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0126Mask : ℕ := 5402559254174376

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0126Witness : Array ℤ :=
  #[148, -38, 8, 30, -72, -15, 27, -33, 6, -29, 190, 24, -50, 145, 40, -21,
  -59, -92, 14, 31, 193, -90, 154, 267, 10, -21, 0, -150, 209, 77, 92, -64,
  87, 81, 19, -42, -125, 42, 31, 63, 119, 3, -136, 101, 93, 78, 127, 12, 37,
  -154, 127, -30, 3, 115, 129, 13, 18, -32, -158, 54, -21, 180, 58, -9, 44,
  68, 4, -150, 139, -17, 193, -12, -73, 259, 36, -34, -37, 68, -47, 53, 48,
  5, 103, 125, 137, 16, -74, 191, -9, -23, 93, -26, 189, -96, 246, -54, 103,
  147, 117, -154, 1, 92, -71, 34, -91, -85, 26, 43, 0, 7, 129, -29, 187,
  119, 125, 22, 32, -23, -121, -230, -140, 7, 77, 90, 71, 135, 90, 181, 55,
  -109, 20, 44, 21, -24, -159, 69, 36, 75, 46, -119, -177, 175, 13, 346,
  250, 48, 3, 85, 47, 129, 0, 86, 71, 48, -61, -44, 65, 34, 53, 29, 151,
  -69, 148, 13, -17, -79, 0, 104]

theorem fractionalNearFrameSubtreeG3R0126_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0126Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0126Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0126Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0126_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0126LowerBoundTable : List ℤ :=
  [338, 394, 504, 315, 553, 17, 305, 393, 491, 294, 309, 703, 27, 471, 426,
  646, 884, 670, 90, 218, 224, -175, 786, 644, 485]

def fractionalNearFrameSubtreeG3R0126LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0126Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0126LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
