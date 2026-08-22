import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0621`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0621Mask : ℕ := 9719314212569676

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0621Witness : Array ℤ :=
  #[-79, -61, 1, 20, -53, -72, 113, 21, -6, -1, -14, -85, -3, -41, -24, 33,
  -97, -85, 0, -30, -81, -159, 45, -51, -45, -71, 78, 103, 52, 137, 17, -50,
  14, -69, 12, -40, 6, 29, 44, 19, 0, 17, -42, 40, 0, 82, 50, -72, -29, -24,
  -68, -30, 76, 7, 34, -3, 16, -23, -39, -25, 5, -24, 46, -3, -120, -41, 12,
  -12, -43, -122, -96, -54, 14, 101, -65, -149, 5, -27, -9, -27, -15, -76,
  -21, 32, 1, -51, -100, -36, -80, -36, -49, 4, 80, 122, -143, -39, -30, 20,
  -15, 31, 1, 23, 17, -17, 45, 45, 66, 34, -47, -8, 79, 43, 174, 126, 52,
  47, 47, -39, 44, 65, 17, 59, 56, 38, 0, -130, 2, -73, 87, -67, 63, -1,
  -29, 34, -43, 17, 13, 2, 38, 86, -51, 38, 23, -57, 120, 13, 31, -28, 16,
  162, 90, -45, -8, -75, -19, 44, 3, 47, -49, 0, -2, -144, -41, -39, 0, -71,
  -118, -104]

theorem fractionalNearFrameSubtreeG2R0621_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0621Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0621Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0621Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0621_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0621LowerBoundTable : List ℤ :=
  [-125, 119, -197, -77, 1, -157, -75, -27, -140, 167, 326, -109, 166, 252,
  -276, 65, -197, -146, -24, -143, 85, -112, -119, 42, -163]

def fractionalNearFrameSubtreeG2R0621LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0621Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0621LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
