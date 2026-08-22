import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0634`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0634Mask : ℕ := 11341164649883146

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0634Witness : Array ℤ :=
  #[-6, 14, -24, -45, 18, -48, 5, 39, 60, 34, 96, -48, 0, -42, 42, -30, 56,
  -14, 81, 42, -8, 13, 20, 3, -7, 38, -2, 53, 28, -77, 59, 51, 28, 17, 15,
  -5, 78, 52, -122, -91, -71, -9, 34, 4, -18, 41, 0, -4, -25, 1, 23, 52,
  -25, -16, 63, 70, 44, 4, -6, -1, 49, 20, -92, -65, -66, -50, -103, 25,
  -37, 17, 19, 47, 27, -7, -22, 51, -40, -24, 55, -19, 8, -13, 41, 49, 79,
  -9, 11, -36, -7, -39, 22, 39, -7, 54, -19, 28, 6, -20, 7, -11, -2, 47, 77,
  56, 18, -25, 29, -43, 51, 0, -8, 53, -54, 19, -17, -16, -28, -30, -13, 6,
  38, -30, -5, 26, 62, -39, -34, 23, -3, 36, 54, -7, 26, 26, -1, -34, 88,
  -59, -41, 43, 27, 16, 43, -70, 82, -41, -28, 12, -42, -52, -27, -6, 87, 1,
  0, 0, -26, -17, 0, 56, -81, 16, 42, -59, -48, 25, -12, 4]

theorem fractionalNearFrameSubtreeG2R0634_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0634Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0634Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0634Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0634_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0634LowerBoundTable : List ℤ :=
  [17, 117, 3, 168, 111, 58, 19, 2, -47, -52, 108, -33, 135, 211, -59, 91,
  -178, -22, 251, -23, 198, 106, 211, 9, 8]

def fractionalNearFrameSubtreeG2R0634LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0634Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0634LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
