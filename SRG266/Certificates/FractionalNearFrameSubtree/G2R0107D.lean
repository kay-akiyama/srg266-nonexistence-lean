import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0107`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0107Mask : ℕ := 1284003696581649

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0107Witness : Array ℤ :=
  #[-93, -59, -36, 14, -12, -67, -37, 63, -80, 39, -16, 57, 38, 88, 21, -40,
  106, 79, 13, 11, -10, -72, -48, 26, 75, 27, 22, 12, -5, 58, -19, 89, -56,
  -93, -62, 23, 84, 82, 61, 56, -43, -34, -91, -45, 128, 63, 21, -96, 27,
  -35, 24, 3, 64, -41, 3, 37, -12, 117, 56, -95, -2, -40, -2, 43, 43, -25,
  -29, 30, 64, -131, -8, -22, 67, 3, -29, 50, 10, -37, 23, -32, -53, 30, 67,
  -18, -26, -63, 56, 15, -16, 24, -74, -29, -179, 5, 12, -67, -78, 29, 2,
  -63, 7, 54, 105, 18, -44, 100, 61, -47, 60, 26, 119, -8, -78, 95, 47, -31,
  83, -10, -56, 43, -14, -41, -51, 17, 2, 6, 13, 8, -3, -41, 77, 8, -1, -25,
  -61, 0, 52, 6, 63, 0, -44, -50, 8, 16, 36, -87, -11, 71, 103, 38, 36, 135,
  -123, 36, 7, 80, -8, -75, -4, -44, -100, -77, 20, -54, -48, 23, -158, 2]

theorem fractionalNearFrameSubtreeG2R0107_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0107Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0107Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0107Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0107_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0107LowerBoundTable : List ℤ :=
  [-26, -31, -60, 3, -29, -38, 213, 2, 2, 10, 332, -45, -155, -153, 10,
  -101, 215, -172, -148, -57, 252, 296, 9, 233, 261]

def fractionalNearFrameSubtreeG2R0107LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0107Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0107LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
