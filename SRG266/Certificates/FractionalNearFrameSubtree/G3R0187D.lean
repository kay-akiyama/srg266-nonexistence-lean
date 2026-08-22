import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0187`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0187Mask : ℕ := 6866712530865676

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0187Witness : Array ℤ :=
  #[-118, -24, 52, -140, -53, 62, 107, 76, 6, 16, 40, 45, 83, 15, 38, 84,
  40, 43, 64, 132, 62, 41, 92, -63, -42, -21, -16, 6, -79, -84, -74, 76,
  -12, 3, 58, 17, 12, -28, 26, -15, 2, 81, 2, 87, -38, 68, 78, -4, -83, -40,
  82, 28, 44, -31, -90, -55, 79, -41, 6, 17, 27, 92, 37, -8, 111, 123, 13,
  53, -63, 62, 0, -68, -4, -1, -5, -117, -99, -105, 106, -30, 0, -42, -60,
  -20, -55, -3, 16, -8, -171, 0, 55, -7, 25, -12, 29, 73, 24, 14, -94, -24,
  50, -8, -14, 12, -4, 19, -22, -19, -60, -69, -55, -27, 16, -3, -49, 39,
  51, 74, 39, 86, -22, -21, -100, 47, -121, -119, -30, 16, -30, 17, 3, -29,
  -45, -106, 38, 25, -37, 21, 34, 20, -52, 51, 31, 134, 10, -14, -24, 47,
  89, 9, 125, -78, -15, -21, -39, 17, 16, 36, -41, 22, -39, -48, 8, 34, -20,
  18, -29, -118]

theorem fractionalNearFrameSubtreeG3R0187_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0187Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0187Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0187Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0187_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0187LowerBoundTable : List ℤ :=
  [-72, -98, -117, -117, 2, 2, 79, 121, 88, 202, 141, 29, -121, 139, -65, 9,
  -1, -110, 19, -50, 55, 314, 202, 266, 454]

def fractionalNearFrameSubtreeG3R0187LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0187Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0187LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
