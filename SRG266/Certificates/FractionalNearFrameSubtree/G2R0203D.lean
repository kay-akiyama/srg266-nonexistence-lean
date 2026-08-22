import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0203`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0203Mask : ℕ := 2348310632829025

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0203Witness : Array ℤ :=
  #[-132, -114, -74, -33, -153, 70, -89, -2, 114, 75, 0, 43, 73, 84, -52,
  15, 98, 20, 99, 38, 20, -23, -91, 63, -57, 44, 3, -42, 48, 37, 21, 60, 32,
  130, 119, 81, 331, -83, -131, -210, -26, -103, 25, 56, 21, -158, -150, 30,
  -15, 36, 91, 52, -46, -51, 38, 15, -59, -38, 40, 65, 46, 53, 50, 21, -26,
  14, -42, -17, 18, 58, 15, 0, 19, -20, 25, 26, -80, 66, 2, 76, 40, 6, -12,
  25, 7, 7, -44, -2, 12, -29, -56, 33, 36, 46, 0, 158, 59, -81, 10, -119,
  -78, -34, -38, 51, -52, -47, 0, -11, 77, 3, -8, -21, 32, 41, -58, 153,
  -75, -93, 56, 41, 91, 49, 43, 107, 15, -26, -51, 61, -13, 27, 20, 23, -24,
  -19, 28, 0, 16, -76, 59, 54, 83, -7, -15, 21, 40, -31, 150, 77, 58, 11,
  31, 88, 35, 24, 32, 0, -25, 0, -34, -98, -1, 16, 32, -75, -33, 97, 0,
  -140]

theorem fractionalNearFrameSubtreeG2R0203_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0203Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0203Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0203Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0203_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0203LowerBoundTable : List ℤ :=
  [47, 221, 14, 153, 3, 62, 242, 2, -28, 160, 365, 191, 224, -34, 116, 16,
  220, 11, 156, 112, 177, 134, -114, 254, 31]

def fractionalNearFrameSubtreeG2R0203LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0203Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0203LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
