import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0584`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0584Mask : ℕ := 6850696666661480

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0584Witness : Array ℤ :=
  #[91, -106, 64, -32, 32, -10, 11, 36, -77, 74, 74, 45, -73, -42, 181, 71,
  11, 84, 0, 14, 20, -46, -38, -79, 94, -35, -20, 26, 146, 141, 182, 147, 0,
  -43, -376, -226, -278, 70, 193, 216, 5, -182, -124, -146, 68, -50, 128,
  152, -103, -208, -45, -104, 171, 333, 25, -9, 75, -4, 84, 108, 130, -14,
  29, -44, 22, 112, 94, 49, -24, -36, -9, -7, 109, 109, 28, 42, 39, -24,
  -65, 61, 37, -3, 0, -34, -62, 30, -50, 46, -6, 119, -24, 130, 68, -25, 4,
  31, -119, -97, 25, 58, 40, -6, 63, -56, -45, 53, 109, 146, 17, -33, -70,
  82, 127, 24, 46, 34, -60, -54, -145, -3, 56, 123, 219, -29, -1, 79, 32,
  -90, 114, 132, 97, 75, -8, 30, -1, 66, 60, 88, 114, 75, -39, 224, 34, -87,
  103, -236, 42, 8, -32, -84, -187, 45, 71, -86, 42, -102, 174, -101, -44,
  122, 78, 49, 33, 67, 143, -20, 41, -25]

theorem fractionalNearFrameSubtreeG2R0584_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0584Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0584Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0584Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0584_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0584LowerBoundTable : List ℤ :=
  [207, 300, 279, 165, 2, 148, 129, 356, 1, 82, 393, 464, 473, 492, 398,
  1038, 455, -429, 377, 277, 45, 282, 121, 10, 515]

def fractionalNearFrameSubtreeG2R0584LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0584Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0584LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
