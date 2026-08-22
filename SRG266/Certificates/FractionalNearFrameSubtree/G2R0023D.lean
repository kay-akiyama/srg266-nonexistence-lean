import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0023`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0023Mask : ℕ := 747308959383633

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0023Witness : Array ℤ :=
  #[9, 32, 42, -45, 35, -16, 0, 0, -71, -44, -107, -58, 122, 10, 20, 17,
  -36, -69, 74, 1, -3, -30, -22, 1, -23, -45, -28, -50, 25, 12, 35, 45, -91,
  15, -147, 13, -71, 97, 38, 83, 17, -79, -11, -182, -40, 114, 143, 38, 15,
  7, 40, 63, -46, -86, 36, -48, -54, 36, 37, 42, 10, -31, 14, 3, 23, -11,
  15, 10, 2, 24, -12, 0, 36, 24, 26, -32, 11, 17, 28, -24, -2, -3, 34, 27,
  12, 25, 11, 29, -16, 36, -2, -29, 31, 8, 23, 9, 7, 12, -10, -10, -59, 38,
  23, -21, 3, 32, 26, -59, -44, -49, -47, -34, 21, 12, -19, -21, 20, 2, -18,
  52, -88, -43, 27, 7, 33, -12, 38, -28, -25, -13, 0, -25, -13, -3, 41, 18,
  35, 29, -15, -27, -30, 46, 30, 37, -16, -23, 19, 49, -57, 23, 37, 51, -23,
  -13, -17, -35, -70, 10, -12, -30, -6, -24, 0, -6, -33, 30, 51, 6]

theorem fractionalNearFrameSubtreeG2R0023_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0023Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0023Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0023Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0023_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0023LowerBoundTable : List ℤ :=
  [-73, -22, 45, 50, -131, 2, -21, 2, 122, -1, 25, -110, -162, 93, -13, 159,
  9, 10, 9, 98, 29, -58, 69, 10, -93]

def fractionalNearFrameSubtreeG2R0023LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0023Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0023LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
