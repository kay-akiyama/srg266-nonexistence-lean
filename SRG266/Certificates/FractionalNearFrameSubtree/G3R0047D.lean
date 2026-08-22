import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0047`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0047Mask : ℕ := 960547193033354

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0047Witness : Array ℤ :=
  #[-45, 17, -8, -164, -6, -71, -35, -37, -138, -86, -89, 31, 5, 45, 11,
  234, -38, -100, -19, -70, -102, 109, 78, 209, -2, 57, 21, 24, -19, -120,
  -64, 145, -14, 3, -23, 61, 18, 64, -163, 10, 58, -41, -131, -94, 74, 61,
  90, -17, 33, 24, 20, 118, -19, 31, -6, -35, -106, 89, 63, 69, 63, -50,
  -100, 50, 25, 62, 180, -34, -16, -40, -22, -77, 43, 38, -13, -78, 30, -44,
  -12, -1, 3, 17, 53, 0, 55, 108, 62, -140, 33, -87, -137, 72, 104, -159,
  10, -93, -67, -20, -11, 5, 71, 75, 32, 96, 7, -49, -130, -94, -32, 85,
  -78, 69, -67, 13, 28, 38, 17, -10, 14, 76, -28, -47, 7, -30, -98, -97, 80,
  19, -108, -7, -1, 29, 68, -89, -36, -86, 48, 7, 166, 96, 51, -84, 83, 2,
  65, 159, -38, 4, -4, -32, -5, 125, -13, 19, -151, 34, 51, 102, -82, -68,
  0, 208, -32, -199, 32, 77, -73, 97]

theorem fractionalNearFrameSubtreeG3R0047_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0047Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0047Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0047Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0047_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0047LowerBoundTable : List ℤ :=
  [-65, 54, 2, -56, 186, -42, -126, -54, -3, 10, 78, -2, 29, 572, 209, 10,
  -322, 187, 9, -219, 122, 204, 10, 92, 152]

def fractionalNearFrameSubtreeG3R0047LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0047Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0047LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
