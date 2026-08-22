import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0342`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0342Mask : ℕ := 5645839168164113

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0342Witness : Array ℤ :=
  #[-127, 24, -122, -12, 0, 32, -153, -98, -24, -98, -52, 4, 3, 180, 106,
  111, 15, 145, 1, 56, 61, 21, 88, 11, 78, -7, -60, -16, -14, -53, -85, 3,
  76, -75, 74, -35, 61, 43, 35, 48, -10, 5, 83, -76, -29, -6, 96, 29, 56,
  24, -36, 2, -4, 2, -24, -39, -42, 89, 85, 14, 48, -60, -53, 11, 72, -35,
  -77, 40, 85, -55, -13, 11, 8, 5, -6, 8, 58, 57, 3, -14, 1, 4, 49, 12, 31,
  -43, 11, -25, -53, 0, 45, -49, -9, 2, -63, 26, -45, 84, -4, 55, 38, -1,
  -40, -20, 1, 69, 29, -129, -50, -53, -96, -47, 64, 55, 68, 259, 18, -9,
  -45, 11, 57, 101, -35, 30, -23, 37, -32, 1, 55, 38, -18, -43, 15, 8, 23,
  -37, -19, 15, -27, 36, 114, 123, 43, -55, 53, 86, 17, -18, 65, 4, 64, 17,
  62, 8, 40, -43, 40, -3, -63, -40, 10, -8, 0, -57, 89, 8, -15, -64]

theorem fractionalNearFrameSubtreeG2R0342_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0342Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0342Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0342Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0342_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0342LowerBoundTable : List ℤ :=
  [35, 160, 73, 2, 133, 203, 2, -67, 2, 201, 268, 336, 192, 22, 51, 197,
  117, 73, 126, -60, 262, 134, 73, 438, 260]

def fractionalNearFrameSubtreeG2R0342LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0342Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0342LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
