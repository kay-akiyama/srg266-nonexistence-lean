import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0170`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0170Mask : ℕ := 2517141459747412

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0170Witness : Array ℤ :=
  #[20, -41, 29, -71, -66, 40, -4, 45, -25, 16, 42, 85, 70, 70, 20, 33, -22,
  -77, -63, 12, 63, 40, 71, 18, 19, -7, 7, 63, 16, -50, -48, -76, -40, -31,
  -5, 23, -5, -58, 22, 30, 118, -15, 46, 15, -27, 2, -43, -20, -12, -58, 54,
  -23, -5, -14, 29, 1, -17, -14, 10, -33, -16, -5, -76, 25, -9, 130, 73, 49,
  0, -19, -2, 29, 19, -38, -28, -19, -21, 75, 43, 71, -8, -39, 81, 53, 19,
  4, -21, 93, 41, -23, -18, 21, -6, 23, 54, 18, -11, 28, 27, 50, 47, -21,
  -14, 12, 50, -24, -41, 52, -12, -77, 21, 25, 10, -33, 64, -51, -15, 16,
  16, -36, 81, -10, -37, -3, -12, 24, -58, -46, 55, -24, 43, -5, -26, 8, 40,
  27, 34, 38, 8, 23, 21, 143, -9, 8, 22, -81, 0, -86, -23, -35, -75, 26,
  -20, -31, -95, 23, 2, 21, -51, -41, -4, -7, 61, 7, 21, 13, -1, -42]

theorem fractionalNearFrameSubtreeG1R0170_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0170Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0170Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0170Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0170_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0170LowerBoundTable : List ℤ :=
  [19, 1, 103, 100, 13, -5, 18, 51, 65, -15, -85, 50, -138, -61, 275, -3,
  50, 380, 200, 159, 181, 44, 101, -3, 219]

def fractionalNearFrameSubtreeG1R0170LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0170Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0170LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
