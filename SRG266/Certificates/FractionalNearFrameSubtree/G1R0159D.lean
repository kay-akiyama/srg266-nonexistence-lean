import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0159`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0159Mask : ℕ := 1866781272214290

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0159Witness : Array ℤ :=
  #[187, 211, 270, 214, 422, 212, -9, 39, 33, -30, 0, 100, -352, -271, -154,
  -318, -213, -129, 146, -260, -9, -103, 54, -7, -48, 14, -97, -142, 158,
  273, 152, 220, -90, 46, -42, 72, -9, -102, 122, 42, 101, 68, -15, 47,
  -119, -55, 49, 68, 59, 115, -78, -119, 93, 57, 21, 0, -47, 15, -30, 8,
  -20, -5, 101, -14, 104, 108, 20, 115, -95, 50, -9, 24, -75, 111, -3, -9,
  103, 6, -96, -125, -96, -16, 113, -108, 135, -93, 60, 41, -54, -88, 68,
  -16, 49, -123, 43, -94, 21, 142, -158, -55, -46, 35, 107, 135, -11, 109,
  -9, 164, 9, 4, 87, 74, -61, 99, 23, 48, -42, 55, 71, -32, 45, -57, -70,
  182, 65, 233, 5, 20, -36, -5, 48, 169, 36, 41, 175, -4, 48, -44, -30, 55,
  64, 22, -8, -38, -47, 6, 50, 24, 11, -29, -7, 105, 132, -121, -74, 77,
  -124, -75, 45, 38, -136, 104, 92, 155, 25, 45, -54, -47]

theorem fractionalNearFrameSubtreeG1R0159_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0159Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0159Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0159Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0159_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0159LowerBoundTable : List ℤ :=
  [128, 244, 203, 227, -70, 480, 2, 306, 40, 524, 175, 411, 381, 373, 314,
  576, 74, -124, -371, 687, 103, 406, 202, -63, 365]

def fractionalNearFrameSubtreeG1R0159LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0159Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0159LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
