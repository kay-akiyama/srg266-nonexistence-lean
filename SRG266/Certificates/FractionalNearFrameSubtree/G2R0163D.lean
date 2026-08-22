import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0163`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0163Mask : ℕ := 1380055422190668

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0163Witness : Array ℤ :=
  #[-84, -247, -128, -14, -152, -73, 108, 96, 16, -35, -47, 88, 141, -49,
  49, 248, -50, -294, -124, -91, -169, 6, 41, 102, 29, -92, 137, 121, 315,
  72, -29, 76, 74, 160, 30, -150, -17, -81, -35, 75, 108, -176, -156, 66,
  -256, -178, -85, 53, 14, 164, 82, 74, 162, -42, -27, 200, -186, -110, -63,
  178, 36, 0, 23, 49, -30, 35, -6, -36, -77, 80, 63, 64, 28, 45, 41, 97,
  -17, -55, 34, 60, 210, -78, -25, 76, -196, -142, -35, -42, 72, 50, -1,
  -22, 98, -75, -7, -97, 65, 15, -107, -24, -119, 35, 2, -17, 29, -102,
  -147, -35, 26, -52, 5, -16, 70, 54, 145, -15, -20, 9, 54, 178, 91, -175,
  -9, -22, -151, -50, -25, 117, 9, -90, -95, -63, -64, 48, 47, 7, 20, 90,
  -20, -23, 238, -53, -32, 77, 199, -1, 126, -21, 65, 105, 58, 8, -98, 200,
  -34, 51, 101, -125, 17, 42, -55, -154, -116, 75, -66, -77, -109, -64]

theorem fractionalNearFrameSubtreeG2R0163_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0163Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0163Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0163Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0163_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0163LowerBoundTable : List ℤ :=
  [-141, 24, -164, 61, -126, -8, 3, 2, -30, -186, 98, 163, 212, 11, 11,
  -282, -276, 157, 61, 10, 901, -180, 570, 169, 215]

def fractionalNearFrameSubtreeG2R0163LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0163Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0163LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
