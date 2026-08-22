import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0326`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0326Mask : ℕ := 5390546028323248

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0326Witness : Array ℤ :=
  #[60, 172, -47, 104, 99, -39, -35, 108, 95, 9, -43, -125, 33, 121, -67,
  131, 138, -70, 95, -12, 24, -68, 65, -11, 87, 34, -7, 135, 107, -24, -83,
  101, -24, 176, 112, -13, 45, 51, 126, -49, 306, 166, 144, 127, 67, -109,
  -232, -138, 110, -43, 31, 222, -133, -132, 198, 184, -32, -177, -43, 36,
  -28, -56, 14, -39, -127, -48, -59, -78, 29, 22, -35, -16, 70, 97, -11,
  191, 73, 120, -30, 47, -51, 162, 75, -110, -75, 73, 33, -31, -16, -15,
  133, -25, -34, -6, -10, -1, -161, 63, 110, 83, -47, 97, 0, 125, 110, 64,
  9, -203, -1, 139, 192, 86, 15, 127, 173, 168, 87, 5, -46, 34, -40, 68,
  -67, -147, 39, 87, 113, 120, 0, -125, -65, 21, -73, -48, -20, 8, 88, 49,
  5, -119, 139, 76, 46, 4, 8, -25, 136, -19, 136, 16, 68, 99, 269, -37, 79,
  62, -56, 51, -12, 46, 67, -5, -120, 31, 30, 102, -42, -185]

theorem fractionalNearFrameSubtreeG2R0326_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0326Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0326Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0326Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0326_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0326LowerBoundTable : List ℤ :=
  [288, 214, 355, 104, 202, 525, 351, 344, 292, 322, 342, 576, 347, 381,
  158, 299, 465, 496, 615, -71, 274, 136, 426, 89, 502]

def fractionalNearFrameSubtreeG2R0326LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0326Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0326LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
