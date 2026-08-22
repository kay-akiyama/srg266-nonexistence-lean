import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0136`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0136Mask : ℕ := 1022440072908050

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0136Witness : Array ℤ :=
  #[-51, 25, 32, 29, 98, 130, -73, 0, 50, 49, 7, -30, -111, -71, -49, -60,
  -27, -107, 31, 10, -30, 71, 53, 30, 15, 84, 19, -49, -38, 119, -38, -40,
  -26, -14, -35, 112, 51, 46, -34, -10, 13, 30, -58, -43, 55, -42, -46, 63,
  88, 18, 16, 49, -19, 39, -55, -11, 136, 140, -87, -49, -111, 0, -56, 31,
  18, -27, -30, -22, 79, 39, -39, -23, -22, 14, 1, -49, 31, 10, 60, -9, 26,
  65, 32, 13, 19, -31, 17, -50, -15, -16, -49, -54, -29, 11, -14, -22, -45,
  73, -58, 14, 20, 2, 35, 19, -7, -43, 41, -3, -45, -76, 54, -4, 32, 5, 7,
  12, -12, -37, -33, -73, -17, 28, -38, -6, 16, 43, -2, 42, 50, 120, 30, -2,
  43, -45, -38, -17, 0, -8, 31, 32, 9, -25, 14, 19, 54, 19, 21, 13, 56, 82,
  31, 35, 4, 29, 70, -7, 26, 10, 44, 20, -204, 65, 97, 97, 110, 92, 122, 28]

theorem fractionalNearFrameSubtreeG1R0136_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0136Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0136Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0136Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0136_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0136LowerBoundTable : List ℤ :=
  [74, 263, 132, 2, 68, 3, 168, 2, -82, 338, 355, 161, 27, -3, 200, 125, 52,
  67, 45, 72, -106, 131, 206, 187, 287]

def fractionalNearFrameSubtreeG1R0136LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0136Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0136LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
