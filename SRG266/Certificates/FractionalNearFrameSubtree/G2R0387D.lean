import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0387`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0387Mask : ℕ := 5739223301448088

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0387Witness : Array ℤ :=
  #[29, 42, 44, 37, -1, -64, 3, 17, 71, 88, -19, -21, -126, -68, -17, 37,
  -2, -23, 2, -105, 27, -69, -20, -3, 65, 6, 142, 20, -1, -16, -7, 4, -22,
  116, 31, -148, -72, -93, 41, 67, 34, -21, 28, -30, -15, 45, -37, 14, -82,
  -41, 39, -20, 16, -97, -30, -28, 48, 140, 0, -15, -25, 3, -86, -28, 14,
  -13, 4, -21, 18, 118, -81, 70, 38, 7, -32, 7, -70, 20, 16, -11, -35, -39,
  -3, 75, -33, 9, -10, -47, 23, 25, 83, 9, 62, -42, 27, 16, 60, -29, -65,
  -14, 57, 57, 14, -26, 19, -7, 22, -41, -84, -71, 2, -69, -28, 110, 140,
  -7, 82, 74, -42, 45, -7, 64, -73, 12, 31, 43, 6, 9, 8, -1, 59, 34, 42, -5,
  -3, -56, 14, 65, 0, -1, -29, 0, 56, 29, 43, 14, -60, 85, -19, 49, 107, 88,
  6, 60, -35, -71, 6, 1, 41, 0, 78, -10, 9, -42, -22, 54, 62, -22]

theorem fractionalNearFrameSubtreeG2R0387_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0387Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0387Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0387Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0387_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0387LowerBoundTable : List ℤ :=
  [-14, 153, -56, 55, 102, 98, 21, 86, -42, 452, 438, 233, -92, 142, 323,
  -67, -90, 164, 100, 187, -115, 10, -47, 155, 10]

def fractionalNearFrameSubtreeG2R0387LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0387Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0387LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
