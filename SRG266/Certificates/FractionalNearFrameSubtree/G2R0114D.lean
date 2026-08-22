import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0114`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0114Mask : ℕ := 1309979658013713

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0114Witness : Array ℤ :=
  #[-160, -182, -80, 1, -176, 49, 65, 16, -18, 102, 39, 0, -81, 97, 48, 85,
  -105, 0, -119, -133, -84, -7, -56, 90, 27, 1, -32, 100, -30, 2, 89, 144,
  -13, 28, 90, -114, -102, -63, -154, -61, -47, 120, 45, 105, 0, -82, 119,
  22, -21, -7, -91, -25, 108, 180, -20, 154, 45, 3, 105, -3, -28, 52, 4,
  -130, -20, 103, 4, 102, 32, 22, -71, 80, -55, 8, 91, 101, 5, -14, 178,
  -161, -64, -37, -14, 86, -85, 19, 59, -4, 135, -23, 96, -22, 63, -23, 67,
  163, 44, 149, 41, 233, -64, 77, -7, -43, -59, -137, -278, -93, 53, -6, -4,
  13, -58, -134, -46, 105, -29, 174, 85, -83, -27, -137, 19, 80, 34, -46,
  26, -29, -65, 6, 101, -74, 26, -154, 272, 141, -19, 38, -119, -62, 32, 16,
  -118, -6, -88, -8, 0, 145, -86, -45, 12, 67, 130, -120, -172, -92, 47, 50,
  -60, -126, -5, -40, -27, 84, 0, 183, -57, -191]

theorem fractionalNearFrameSubtreeG2R0114_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0114Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0114Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0114Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0114_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0114LowerBoundTable : List ℤ :=
  [-54, 55, 17, 229, -63, -154, 1, 2, -39, 49, -25, 16, -324, -179, 464, 46,
  374, 219, 131, 348, -248, 82, 10, -240, 120]

def fractionalNearFrameSubtreeG2R0114LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0114Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0114LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
