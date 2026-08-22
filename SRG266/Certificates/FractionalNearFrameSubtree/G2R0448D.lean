import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0448`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0448Mask : ℕ := 5792746595336842

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0448Witness : Array ℤ :=
  #[-74, 42, 82, 72, 106, 108, 82, 79, 39, 128, 170, -148, -202, -112, -53,
  -72, 11, 51, 77, 80, 33, -84, -131, -107, -117, -107, 127, 121, 89, 149,
  -23, -59, -51, -1, 39, 152, 62, 50, -67, 3, 49, 63, 69, -16, 17, 26, 10,
  -31, -2, 77, -52, 42, -80, 32, 6, 34, -64, -86, -31, 28, -32, 69, 35, 27,
  18, -45, 57, 130, 88, 18, 59, -110, 218, -55, 12, -57, -49, 79, 3, -15,
  -6, 14, 73, -55, -14, -2, 107, -141, 94, -2, 139, 78, -61, 121, 36, 52,
  -69, -43, 45, 93, -31, -21, 34, -2, 45, 77, 24, 48, -12, 12, -21, -42,
  -69, 77, 16, 17, -8, 45, 50, -10, 21, 79, 46, 8, -5, -32, 11, 32, 4, 32,
  59, 3, 69, 58, 76, 0, -18, 78, -19, 107, -27, 34, 2, -43, 10, 4, 34, 25,
  33, 0, 15, 20, 12, 59, -21, -53, -55, 73, -103, -45, 120, 55, 85, 21, -36,
  -28, 31, -51]

theorem fractionalNearFrameSubtreeG2R0448_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0448Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0448Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0448Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0448_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0448LowerBoundTable : List ℤ :=
  [149, 142, 151, 242, -28, 231, 127, 118, 155, 201, 137, 343, 282, -176,
  104, 26, 492, 252, 512, 11, 1080, 15, 498, 183, 52]

def fractionalNearFrameSubtreeG2R0448LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0448Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0448LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
