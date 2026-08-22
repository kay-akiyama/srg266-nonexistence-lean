import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0001`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0001Mask : ℕ := 242834919252229

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0001Witness : Array ℤ :=
  #[-67, -183, 172, 138, 27, 115, -18, -104, 155, -20, 106, -312, 152, -70,
  90, 168, -169, 105, 17, -132, 12, 97, 25, 51, 278, -21, 309, -154, 107,
  -9, 88, -28, -149, -349, -143, -46, 56, 4, 384, 172, -8, -239, -224, 0,
  373, 85, 21, 50, -20, -35, -41, -66, -137, 72, 358, 178, -160, -55, 147,
  100, 114, -109, 101, 210, 74, 190, -34, 170, -38, -52, 92, -42, -183, 70,
  48, 108, 119, 33, -5, 195, 37, 68, 43, -140, -288, 50, 38, -188, -17, 91,
  -82, -71, -69, -233, 123, 197, 54, -46, -46, -7, -39, -128, -64, 0, 108,
  -24, -26, 62, 204, -23, 0, 90, 115, 64, 43, -125, 144, 112, 35, 271, 216,
  -91, -72, 122, 201, 82, -47, 116, 576, 23, 122, 94, -183, 268, 41, 34, -9,
  81, 223, 247, 207, 17, -80, 290, -12, -97, -99, -98, 174, 243, 353, 214,
  138, 115, -186, 70, -4, 36, 91, -214, 133, 180, -350, -70, -10, 72, 49,
  -41]

theorem fractionalNearFrameSubtreeG1R0001_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0001Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0001Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0001Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0001_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0001LowerBoundTable : List ℤ :=
  [250, 666, 116, 424, 402, 2, 442, 613, 538, 921, 1205, 1086, 315, 787,
  -374, -80, 148, 460, 111, 760, 636, 118, 789, 454, -41]

def fractionalNearFrameSubtreeG1R0001LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0001Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0001LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
