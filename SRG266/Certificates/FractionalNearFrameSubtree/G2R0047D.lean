import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0047`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0047Mask : ℕ := 931066780685458

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0047Witness : Array ℤ :=
  #[155, 212, 41, 37, 105, -26, -32, -38, -51, -24, 9, -23, 79, -226, 3, 0,
  53, 17, 166, -115, -159, 121, 139, -99, -144, -249, 213, -90, 368, 93,
  257, -122, -15, 117, 74, 30, 181, 29, -69, -81, -56, -45, 265, -129, -164,
  152, 78, 175, 108, 140, -62, -202, -119, -86, 114, 114, -204, -94, -178,
  -128, 3, -16, -222, -95, -260, 9, 0, 179, -23, 167, -67, -213, 65, 34,
  -27, 104, -177, 237, -184, 75, -6, 130, -5, 38, 225, 34, 12, 72, -40,
  -192, 27, 102, 42, -41, -94, -52, 227, 2, -101, -166, 192, 54, -72, -34,
  68, -35, 115, 163, 159, 80, -187, -79, -144, -17, 18, 179, -97, -14, 214,
  180, -109, -15, 107, -116, -157, 161, 47, -49, 46, 17, 80, -15, 181, 5,
  -60, -128, 179, 0, 82, 58, -288, 82, 181, -49, 189, 117, 104, -72, 57,
  -188, 100, 103, -25, -312, -113, -82, -31, 98, -20, -85, 98, 75, -35,
  -200, -6, 115, -108, 30]

theorem fractionalNearFrameSubtreeG2R0047_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0047Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0047Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0047Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0047_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0047LowerBoundTable : List ℤ :=
  [-218, 134, -306, 2, 1, 201, 1, 357, 75, 10, 231, 465, -324, -417, 519,
  -123, 268, -96, -260, 825, -251, 670, 603, 546, 440]

def fractionalNearFrameSubtreeG2R0047LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0047Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0047LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
