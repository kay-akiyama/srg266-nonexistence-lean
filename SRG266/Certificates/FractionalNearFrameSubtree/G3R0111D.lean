import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0111`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0111Mask : ℕ := 5385254661198226

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0111Witness : Array ℤ :=
  #[79, 47, 56, 42, 44, -21, -10, -25, 38, 45, -30, 37, -71, -114, 20, 15,
  -58, -59, 35, -44, -19, -15, 28, 64, 165, 40, 49, -60, 20, 70, 45, 23,
  -65, 14, 24, 74, 10, -11, 4, -38, -36, -72, -52, -26, -95, 17, 67, 17,
  -24, 39, 64, 15, 31, 11, -43, -55, 47, 43, 37, 32, -75, -47, 26, 16, 7,
  -56, 46, 17, -32, 18, 62, -22, 5, -27, 37, -28, -13, 24, 69, 2, 39, -41,
  10, 36, -32, 23, -17, -10, -16, 2, -2, -67, 56, 26, -63, 12, 24, -15, -7,
  -75, -13, -32, 106, 130, 77, 99, 53, -21, 13, 111, -15, 30, -35, 47, -10,
  25, -111, -45, 90, 35, -5, 52, -6, -81, -53, 2, -33, 15, 83, 19, -9, 14,
  -20, -29, -21, 21, 30, 86, -58, -49, -48, -45, -5, 44, -23, 70, 39, -57,
  5, 64, 13, 24, 24, -44, -61, 53, -38, 70, 53, 16, 16, -44, -80, 5, 0, -12,
  0, -37]

theorem fractionalNearFrameSubtreeG3R0111_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0111Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0111Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0111Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0111_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0111LowerBoundTable : List ℤ :=
  [-28, 1, 6, 250, 17, 12, 2, 22, 160, 9, 49, -22, 152, -153, 228, 10, 92,
  243, 149, 9, 396, 10, 99, 21, 211]

def fractionalNearFrameSubtreeG3R0111LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0111Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0111LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
