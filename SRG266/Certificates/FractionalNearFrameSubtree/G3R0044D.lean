import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0044`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0044Mask : ℕ := 957042743086226

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0044Witness : Array ℤ :=
  #[181, 118, -19, 62, 87, 116, -146, -117, 94, -195, -6, -20, 32, -72,
  -159, -166, 53, 131, -82, -137, -144, 78, -111, 9, -243, -92, 249, 49,
  144, 77, 72, 2, 22, 174, 53, -156, -61, 68, 92, 10, -112, -71, -97, -32,
  174, 25, 118, -18, 192, 161, -104, -73, -206, 41, -5, -103, -79, -65, 0,
  84, 208, -1, 13, 283, 0, -171, 4, -22, 35, -51, -58, 174, 131, 90, -5, 10,
  -27, -206, -52, -64, -62, 41, -13, 100, -98, 63, 16, 220, -8, 9, 96, -19,
  22, 148, -14, 77, -61, 74, 60, 18, -17, 138, -70, -79, 122, -67, -5, -6,
  90, 38, 19, -181, -97, -66, 17, -15, 25, -118, 137, 116, 60, 123, 63, 116,
  39, -69, -70, -96, 67, -48, 6, 143, 51, 3, 87, 93, -5, -38, -41, -168, 58,
  67, -73, -10, 62, 128, 7, 253, 66, 0, -136, 45, 137, 49, -4, 146, 44, -46,
  -4, 36, -182, 100, 110, 130, 20, 7, 125, -132]

theorem fractionalNearFrameSubtreeG3R0044_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0044Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0044Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0044Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0044_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0044LowerBoundTable : List ℤ :=
  [27, 275, 48, 1, 1, 155, 234, 203, 98, 271, 9, 400, 280, 469, 10, -43,
  297, 196, -136, 305, -224, 858, 288, 427, 89]

def fractionalNearFrameSubtreeG3R0044LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0044Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0044LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
