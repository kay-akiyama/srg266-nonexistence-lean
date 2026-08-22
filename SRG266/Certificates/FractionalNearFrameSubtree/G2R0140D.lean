import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0140`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0140Mask : ℕ := 1361654456959626

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0140Witness : Array ℤ :=
  #[-59, -8, -64, -31, 14, -83, 53, 47, -35, -66, -25, 53, 67, 7, 27, 108,
  58, 94, 78, 20, 28, -78, 63, -8, 118, 35, -58, -97, -1, -147, 6, -10, -46,
  -42, 62, 21, -36, 106, 20, -39, 1, 218, 6, 13, -11, -89, 32, 50, 37, 93,
  25, -53, -122, -17, 7, 108, 60, -76, -16, -46, -49, 20, 104, -35, -22, 36,
  -83, 40, -11, -30, 5, 36, 43, 57, -28, 12, 63, 108, -44, -7, -118, 40, 92,
  120, 43, -130, 45, 17, -12, -36, -12, -2, 6, -174, 5, -25, 88, -11, 36,
  -9, -101, 5, 134, -191, 82, 3, -53, -82, -56, 185, 71, -21, 9, 119, 133,
  127, 41, -13, 106, 0, 35, -55, 18, -47, -71, -29, 34, 88, 100, -39, 26,
  29, -122, 36, 9, -84, 112, -56, 148, -4, 2, -20, 22, 75, 7, 42, -144, -31,
  72, -13, -65, 15, -53, -27, 83, 108, 7, -16, -98, -50, 75, 59, 12, 47,
  182, 33, 113, -26]

theorem fractionalNearFrameSubtreeG2R0140_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0140Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0140Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0140Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0140_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0140LowerBoundTable : List ℤ :=
  [31, 183, 106, -36, 34, 34, 2, 168, 80, 9, 452, 313, 252, 130, 118, 285,
  150, 242, 82, 293, 9, 192, 321, 149, 180]

def fractionalNearFrameSubtreeG2R0140LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0140Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0140LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
