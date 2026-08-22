import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0042`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0042Mask : ℕ := 538380898722444

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0042Witness : Array ℤ :=
  #[-35, -203, -98, -113, -172, 64, 130, -4, -105, 74, 154, 101, -14, 80,
  152, 18, -90, 81, -39, -84, -28, -61, 59, -59, -27, 95, 6, 111, 20, 111,
  135, -84, 32, 5, -114, -42, 76, 34, 15, -103, -47, -124, -140, 52, 62, 76,
  -78, 30, 4, -55, 52, 31, -59, 54, 6, 55, 161, -45, -108, 64, 106, 17, 105,
  31, 45, 2, -33, -9, 0, 44, -24, 7, 39, 49, 32, -48, -121, 0, -99, -20,
  -33, 15, 3, 72, 27, -106, -8, 84, 90, 5, -67, 38, 26, -27, -61, 131, 124,
  -67, 145, 92, 116, 135, 28, 8, 3, 70, 103, -83, 6, 30, 28, 28, 73, -46,
  71, 74, 138, -28, -128, -36, 29, 41, -26, 45, -65, -1, 9, 107, 52, 34, 69,
  40, -9, -22, -52, 47, 45, 149, -33, 24, -124, 27, 13, 27, 103, 35, 110,
  -21, 16, -62, -6, 108, -16, 45, 127, 40, 19, 10, 60, 3, -43, -50, 22, -28,
  -17, 80, 4, -38]

theorem fractionalNearFrameSubtreeG1R0042_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0042Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0042Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0042Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0042_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0042LowerBoundTable : List ℤ :=
  [66, 246, 121, 122, 97, 215, 1, 126, 80, 432, 293, 124, 223, 745, -264,
  174, 463, 51, -38, 417, 11, 227, 8, 327, 372]

def fractionalNearFrameSubtreeG1R0042LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0042Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0042LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
