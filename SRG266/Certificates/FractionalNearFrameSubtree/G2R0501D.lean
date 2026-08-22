import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0501`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0501Mask : ℕ := 5811551279354468

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0501Witness : Array ℤ :=
  #[-41, 16, -13, -28, -31, -1, -10, -10, 6, 20, 82, 41, -33, 80, -1, -46,
  -53, 15, -12, -18, -21, 18, -14, 12, 19, 101, -11, 45, -13, -17, -51, -8,
  -64, -20, -14, 24, 43, 56, 22, -7, 43, -13, 78, -19, 66, 6, 6, 5, -30, -5,
  -16, -87, 20, 37, 0, 82, 0, 5, -11, -11, 18, 55, -86, -94, 45, 13, 118,
  -17, -6, -9, 37, -16, 44, -13, -1, 16, -27, 28, 15, 3, -18, 40, -9, -34,
  0, 18, 9, -18, 37, 2, 7, 29, -41, -2, 71, 29, 20, -11, 3, -7, 1, -45, 10,
  -12, 59, 7, -19, 0, 35, 15, 56, -14, 19, -14, -19, -30, -44, 29, 15, -9,
  67, 2, -6, 1, -7, 30, 26, 19, 7, -13, -5, 22, -3, -21, 4, 93, -19, 57, 10,
  14, 0, 87, 91, -24, 3, -29, 45, -130, -51, -33, -57, 11, 13, -22, -66, 23,
  41, 15, 1, 71, -39, -41, -70, 22, 6, 93, -8, 89]

theorem fractionalNearFrameSubtreeG2R0501_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0501Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0501Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0501Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0501_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0501LowerBoundTable : List ℤ :=
  [38, 77, 64, 64, 33, 22, 101, 87, 77, 9, 58, 173, -70, 148, 27, -183, 416,
  12, 131, 123, 57, 82, 0, 10, 10]

def fractionalNearFrameSubtreeG2R0501LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0501Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0501LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
