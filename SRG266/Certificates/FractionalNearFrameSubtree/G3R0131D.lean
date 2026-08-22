import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0131`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0131Mask : ℕ := 5403671637695280

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0131Witness : Array ℤ :=
  #[-25, 52, -63, 18, 44, -197, -64, 82, 72, 124, -42, -41, 39, 79, -189,
  -68, 35, -109, 22, -59, 85, 31, 71, 44, -23, 70, -5, 81, -78, -132, -136,
  -59, 59, 93, 79, 81, 14, 33, -85, -39, 54, 243, 33, -82, 18, 6, -24, 61,
  -91, -46, 53, 105, -65, -54, -3, 74, 160, -180, -7, 0, -103, 80, -63, 72,
  -247, -74, -88, 98, -53, 53, 27, -52, -154, 48, 28, 168, 48, 8, -58, -73,
  72, 117, -39, -7, -115, -78, -19, -31, 25, 131, 160, 64, 104, 25, -175, 2,
  -70, -30, 89, 52, 51, -57, 23, -98, -81, -160, -114, -121, -52, 186, 202,
  -7, 14, 64, -27, 127, 0, 67, -98, -176, 18, -120, -191, -42, -56, 147, 81,
  123, -140, -162, -29, -30, -18, 38, 22, 19, 67, -47, -101, -50, -82, -50,
  -80, -21, 137, -24, 41, 95, -15, 41, 65, -76, 15, -35, -124, -23, -102,
  -158, 17, 13, 114, -91, 97, 46, -43, 17, 0, -268]

theorem fractionalNearFrameSubtreeG3R0131_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0131Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0131Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0131Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0131_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0131LowerBoundTable : List ℤ :=
  [-159, -159, -133, 1, 72, -327, 2, -92, -104, -164, -197, -301, 65, -15,
  272, 103, -72, 184, -175, -125, 66, 164, 55, -279, -69]

def fractionalNearFrameSubtreeG3R0131LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0131Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0131LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
