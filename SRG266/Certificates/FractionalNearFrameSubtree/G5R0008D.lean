import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0008`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0008Mask : ℕ := 805516305211651

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0008Witness : Array ℤ :=
  #[80, 4, 27, -60, -6, 10, -43, -56, -61, -91, -72, 11, -16, 0, 128, 15,
  19, -10, 26, 8, -19, -1, 104, 18, 45, 3, 56, -58, -72, -36, 7, -45, -115,
  -81, 24, -62, 71, 10, 87, 98, -75, -104, 34, 131, 47, -5, -73, -35, 45, 0,
  93, 66, 36, 43, 60, 23, -70, -12, 12, 7, 26, 37, 11, -13, -42, 13, -21,
  29, 15, -19, 44, 16, -26, -20, -24, -57, -21, -54, -22, -40, 46, 39, 107,
  70, 42, -49, 4, -28, 58, 53, 15, 67, 41, 20, -50, 10, -20, 31, -20, 1, 18,
  64, 34, -15, -25, -50, -13, 34, 17, 15, 24, 19, -36, 7, -42, -43, -45,
  -57, -10, -62, 74, 27, 76, 32, 21, -78, 7, 47, 48, 23, 8, -5, 16, 0, -32,
  -27, 17, -2, -12, -42, 10, -38, 42, 39, 0, 31, 34, 76, 10, -63, 22, 20,
  52, 35, -3, -9, -25, -25, 45, 32, 0, -10, 80, 18, -75, -87, 15, -13]

theorem fractionalNearFrameSubtreeG5R0008_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0008Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0008Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0008Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0008_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0008LowerBoundTable : List ℤ :=
  [-4, 33, 69, 102, 2, 81, 1, 23, 42, 77, 22, 189, -112, 318, 2, 301, -224,
  -51, 94, 153, 45, 9, 135, 43, 218]

def fractionalNearFrameSubtreeG5R0008LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0008Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0008LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
