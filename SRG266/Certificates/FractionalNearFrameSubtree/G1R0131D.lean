import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0131`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0131Mask : ℕ := 1022231796425478

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0131Witness : Array ℤ :=
  #[-18, 100, 34, 0, -73, 58, 89, 10, 58, 91, 96, -45, -44, -81, -25, 73,
  -85, -56, -25, 30, 56, -61, 32, 0, -52, -35, -4, -38, 114, 134, 99, 77,
  -22, 23, 17, -7, 42, 25, 21, 71, 1, -9, -36, 20, 7, 24, -8, 74, -9, -86,
  73, 47, 71, -19, -49, -30, -28, -32, -31, 80, 18, 79, -14, -44, -28, 11,
  72, -22, 12, 32, 10, 7, 18, 7, -22, 36, -24, 47, 4, 10, 15, 37, -1, 10, 5,
  26, -28, 9, -19, -24, 3, 31, -11, 75, 60, 18, 4, 6, 26, -37, 27, -21, -42,
  -9, -42, 16, 20, 6, 23, 3, 44, -6, 26, -19, 26, 47, 18, -45, 19, 53, 17,
  32, 37, 75, -2, 48, -7, 14, 30, 60, -10, 65, -3, 0, 9, -50, -67, 70, -9,
  32, 11, 31, 20, 40, -2, -58, 28, -8, 120, 10, -24, 21, -13, -103, -7, 7,
  -13, -49, 74, 47, -79, -72, 13, -3, 3, 24, 66, -52]

theorem fractionalNearFrameSubtreeG1R0131_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0131Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0131Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0131Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0131_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0131LowerBoundTable : List ℤ :=
  [113, 68, 1, 1, 146, 100, 316, 87, 224, 195, 129, 187, 118, 162, 107, 53,
  -153, 10, 219, 29, 148, 115, 396, 71, 272]

def fractionalNearFrameSubtreeG1R0131LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0131Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0131LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
