import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0039`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0039Mask : ℕ := 888014437714017

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0039Witness : Array ℤ :=
  #[62, -129, 0, -127, -126, 96, -12, 225, 308, -140, 164, -6, 10, 112,
  -284, -179, -238, 152, -11, 26, -11, 28, -289, 129, -102, 27, -89, 111,
  120, 189, 208, 32, -22, -20, -111, -28, 56, 118, 38, 260, 97, 0, 103,
  -292, -26, 276, -113, 0, 86, 4, 19, 41, -6, 0, -27, -28, -122, -65, -96,
  24, -21, -35, -37, -103, -10, 102, -69, 63, 43, -43, 10, 68, -101, 156,
  38, 86, -239, -91, 0, 272, 38, 85, 103, 83, -132, 79, 75, 124, -27, 93,
  -5, 164, 18, 9, 71, 114, 33, -156, -262, 275, -26, -2, 78, 30, -33, 114,
  39, -92, -90, -137, 155, -267, -143, -119, 198, -229, -240, 428, 116, 196,
  28, 190, -126, 13, 55, 41, 70, 3, 332, 19, 96, -111, 64, 118, 51, -99,
  -46, 245, -93, 0, 147, -133, 61, -94, -214, 73, 162, 43, 30, 119, 225, 21,
  18, 68, -99, 106, 144, 70, -2, 99, 23, -101, 109, -115, 216, -28, 259,
  333]

theorem fractionalNearFrameSubtreeG2R0039_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0039Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0039Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0039Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0039_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0039LowerBoundTable : List ℤ :=
  [58, 689, 87, 158, 1, 625, 498, 2, 2, 1149, 118, 622, 204, 137, 196, 162,
  221, 585, -394, 170, 215, 428, -458, 1154, 318]

def fractionalNearFrameSubtreeG2R0039LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0039Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0039LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
