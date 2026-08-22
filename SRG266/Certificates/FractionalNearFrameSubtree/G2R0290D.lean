import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0290`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0290Mask : ℕ := 5385226114667666

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0290Witness : Array ℤ :=
  #[145, 149, 67, 58, 113, 21, -85, -62, -38, 67, 74, -170, -119, -121, 0,
  -87, -121, -113, 8, 33, 71, 9, -55, 98, 72, 60, -118, 3, 152, 147, 46, 48,
  -96, -68, -56, 1, 35, -4, 3, -43, 83, -36, 71, -32, 9, -111, -78, 11, -46,
  78, 1, 1, -77, 57, 79, 37, 27, -12, -63, -61, 9, -48, 0, 32, 60, -3, 137,
  29, -35, -4, 21, -27, -46, 77, 101, -39, 21, -70, -72, 53, -32, -28, 124,
  41, 32, -74, -67, -14, -46, -14, -86, 34, 77, -4, -10, 75, -46, 77, -18,
  9, -53, 124, 111, -11, -86, -43, 86, 1, 0, -23, 41, 124, -41, 22, 50, 3,
  80, 58, 5, 27, 35, -54, -3, -31, 54, 37, 61, 80, 60, 18, 79, 44, 1, -21,
  17, -12, 53, 80, 53, 55, 88, 103, 67, 44, -28, -8, 39, -39, 69, 33, -100,
  -23, 51, -89, -56, 17, 78, -53, -60, -90, -54, 70, -28, 0, -25, -47, -69,
  -103]

theorem fractionalNearFrameSubtreeG2R0290_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0290Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0290Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0290Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0290_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0290LowerBoundTable : List ℤ :=
  [66, 88, 24, 287, 63, 3, 18, 129, -24, -24, 347, 218, 86, -102, -98, -39,
  224, 437, 350, 181, 165, -187, 198, -43, 10]

def fractionalNearFrameSubtreeG2R0290LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0290Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0290LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
