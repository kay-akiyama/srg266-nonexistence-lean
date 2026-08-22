import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0076`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0076Mask : ℕ := 971434247168232

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0076Witness : Array ℤ :=
  #[-22, 26, 0, 19, -34, -32, 4, -9, -45, -6, 13, -12, 37, -25, -8, 20, 17,
  26, -1, -84, 2, -68, 26, -16, -6, 40, 24, 32, 15, -73, -18, -101, -32, 9,
  0, 86, 15, 76, 0, -24, -1, 68, 28, -12, -16, 18, 4, -70, -34, -15, 23, 0,
  12, -36, 15, 6, -28, -21, -10, -42, 0, -53, 40, -7, 47, -17, -9, 5, -19,
  -67, -5, 11, 12, -45, -19, 86, -26, -5, 80, -43, -29, 3, 120, 61, -79, 38,
  -55, -20, 66, 13, 9, 11, 12, -28, 99, 30, -17, 60, 104, 40, 98, 13, 3, 0,
  -24, -82, -14, -51, 96, 47, 86, 19, -22, -6, -52, -71, 39, 36, -39, 35,
  29, 0, -38, -7, 23, 26, -6, 4, 82, 59, -4, -10, -23, -22, -46, 59, -56,
  117, 6, 24, -14, -71, 3, -47, -2, 10, -14, -42, -17, 19, -15, -35, 24, -7,
  -7, -18, -33, 131, 15, -21, 30, -42, -1, -15, 85, -27, 6, -12]

theorem fractionalNearFrameSubtreeG2R0076_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0076Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0076Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0076Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0076_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0076LowerBoundTable : List ℤ :=
  [-70, -8, 125, 81, 31, 31, 55, -49, -120, 46, 229, 10, 10, -81, 66, -12,
  379, 218, 32, 44, 10, 127, 10, 9, 10]

def fractionalNearFrameSubtreeG2R0076LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0076Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0076LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
