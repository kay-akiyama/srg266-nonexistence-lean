import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0131`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0131Mask : ℕ := 1353135372739722

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0131Witness : Array ℤ :=
  #[-67, -28, 17, 57, -15, 59, 7, -5, 20, 18, 20, -38, -33, -42, 79, -57,
  -52, -28, -28, -14, -10, -21, 19, 3, -18, 0, 7, 14, 47, -11, -113, -82,
  -56, 47, 104, -9, 24, 20, 53, 43, -63, 36, -79, 4, 26, -35, 7, 60, 71, 26,
  -15, -83, -29, 47, -46, -82, 31, 0, 86, 42, 145, -68, 20, 26, -62, -26, 6,
  4, -8, -3, -44, -1, -3, -43, 28, -14, -56, -12, 17, 69, -37, 48, -38, -69,
  -61, 54, 17, 0, 52, 9, 6, -15, 17, 3, 75, -56, 57, 28, -12, 2, -13, 54,
  -31, -60, 43, -15, -11, -17, -32, -53, -37, 7, 3, 69, 23, -19, 25, 53, 11,
  6, -41, -141, -112, -37, -20, -15, -16, 39, -81, 84, 10, 25, 72, 35, 11,
  -20, -37, 19, -76, 47, -21, 8, 72, 46, -133, -3, -40, 71, -51, 8, -81, 1,
  -40, 62, 35, -36, 31, 52, 59, -4, 76, -37, 91, 69, 72, -119, 6, 11]

theorem fractionalNearFrameSubtreeG2R0131_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0131Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0131Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0131Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0131_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0131LowerBoundTable : List ℤ :=
  [-82, 12, -100, 9, 2, -12, 71, -78, -65, -50, -25, 190, 8, 63, 79, 79,
  -333, 54, 136, 9, -40, 416, 138, 51, 11]

def fractionalNearFrameSubtreeG2R0131LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0131Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0131LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
