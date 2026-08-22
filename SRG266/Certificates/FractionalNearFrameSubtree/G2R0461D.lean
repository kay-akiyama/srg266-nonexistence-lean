import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0461`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0461Mask : ℕ := 5807333079238154

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0461Witness : Array ℤ :=
  #[85, 199, 88, 147, 28, -54, 0, 98, -43, -156, -73, 70, -20, 174, 219,
  -81, -51, 70, -165, 118, -135, 68, 129, 14, 87, 111, 206, 48, -165, -50,
  134, 10, -83, 57, 236, 147, 310, -185, 60, -264, 0, 224, 78, 164, 150, 49,
  -3, -329, -262, -121, 300, 81, -109, -103, -45, 84, 73, 3, 218, -292,
  -243, -48, 217, 62, 61, 370, -63, -27, -39, 70, 108, 262, 188, -127, 0,
  -29, 204, 40, 99, -14, 17, -100, -25, -38, -27, 20, -161, 22, 32, -18,
  241, 137, 111, -9, -106, 83, 100, 100, 75, 168, -2, -25, -64, 125, -90,
  -88, -239, 132, 97, 108, 62, 20, 113, 37, -1, 72, -60, 124, -44, -263, 46,
  79, -57, -66, -36, 83, 97, -17, 0, -110, -133, -217, -46, 57, 90, 161, 11,
  -157, 140, -46, 291, -6, 144, 250, 122, 146, -2, 28, -30, -78, 73, 94,
  232, -5, -204, 13, -183, -62, -24, -122, -130, 64, -6, -271, 127, -121,
  46, -68]

theorem fractionalNearFrameSubtreeG2R0461_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0461Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0461Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0461Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0461_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0461LowerBoundTable : List ℤ :=
  [39, 0, 154, 412, 2, 184, 544, 76, 444, 147, -117, 294, 10, 56, 1032, 308,
  560, 369, 320, 9, 514, -133, 390, 630, 664]

def fractionalNearFrameSubtreeG2R0461LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0461Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0461LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
