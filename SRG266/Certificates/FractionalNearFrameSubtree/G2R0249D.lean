import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0249`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0249Mask : ℕ := 5192535755674008

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0249Witness : Array ℤ :=
  #[-39, 74, 40, 70, 38, 19, -19, -9, 36, 21, -13, -46, -72, -34, -29, 68,
  21, -14, -6, 31, 4, 19, -76, -65, 8, 4, 41, -7, -28, -60, -44, 50, 53, 40,
  87, 18, 35, 21, 67, -20, 65, 104, 94, 22, 49, 41, -56, -30, 2, 2, 12, 3,
  -103, -19, -19, 75, 75, 11, -76, 65, -29, 11, 13, -3, -49, -18, 37, 60,
  31, 8, -3, 34, 91, -27, -65, -4, 10, -36, -83, 36, -52, 20, -86, 79, -46,
  -4, 43, 46, -76, -24, -65, 13, -35, 54, -22, 0, -41, 34, 4, 55, 33, 15,
  16, -30, -10, -40, -8, -53, -3, 9, 36, -83, -2, 3, -58, -91, -81, -4, 64,
  26, 16, -21, -38, -36, -38, 16, 20, 22, 67, -21, 0, 24, 20, -42, 29, -47,
  -26, -103, -55, -1, -13, -3, 9, -14, 27, -9, 66, -8, 3, 7, -11, -19, 46,
  -8, 21, 54, -10, 17, -43, 6, 0, 32, 8, -8, 12, 15, 15, 10]

theorem fractionalNearFrameSubtreeG2R0249_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0249Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0249Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0249Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0249_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0249LowerBoundTable : List ℤ :=
  [-78, -40, 1, -2, -20, 88, -43, 27, -19, 9, 113, -72, -198, 71, 236, 92,
  207, 99, 10, 196, 164, -81, 9, 145, 194]

def fractionalNearFrameSubtreeG2R0249LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0249Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0249LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
