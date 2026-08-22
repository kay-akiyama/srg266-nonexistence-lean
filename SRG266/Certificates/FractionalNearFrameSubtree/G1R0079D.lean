import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0079`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0079Mask : ℕ := 898807555804169

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0079Witness : Array ℤ :=
  #[-35, 0, -42, -70, -38, -53, 3, 90, 94, -20, -70, 132, 67, 0, -7, 33, -5,
  -54, -29, 103, 162, 11, 46, 10, 18, 32, -68, -135, 42, -46, 49, 74, -27,
  27, -7, 111, -153, -95, -44, 26, 10, 76, 47, 44, 10, -69, -54, -12, 77,
  -1, 43, 72, 33, -51, 23, -21, -39, -33, -24, 24, 52, 8, 25, 48, -17, -11,
  -7, 22, -28, 67, 18, -79, -28, 35, -7, -68, 4, -13, 64, -24, -12, -22, 24,
  -14, 2, -77, 60, -78, 121, -54, -56, -9, 142, 96, 37, 69, 3, -26, 130,
  -84, -6, -8, -2, 62, -5, -55, 104, 133, 83, 55, 130, 117, -47, 3, 8, 141,
  48, -95, 51, -103, -10, 7, 67, 19, -88, 195, 61, 28, -38, -68, 96, -84,
  -30, 50, -93, -75, 11, -40, 25, 46, 26, -5, 13, 140, 46, 42, 78, -35, -37,
  48, -66, -39, -8, 9, 26, -28, 147, 25, -11, 173, -3, -46, -26, -5, 68, 55,
  125, -31]

theorem fractionalNearFrameSubtreeG1R0079_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0079Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0079Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0079Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0079_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0079LowerBoundTable : List ℤ :=
  [74, 226, 184, 2, 9, 381, 2, 231, 71, 516, 305, 347, 104, 349, 149, 221,
  246, -109, 78, -15, 221, 59, 54, -48, 121]

def fractionalNearFrameSubtreeG1R0079LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0079Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0079LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
