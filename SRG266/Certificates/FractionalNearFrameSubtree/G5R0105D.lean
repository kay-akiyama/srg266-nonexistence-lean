import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0105`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0105Mask : ℕ := 5731035624742985

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0105Witness : Array ℤ :=
  #[71, -199, -102, -112, 18, -94, 47, 125, 201, 101, 254, -106, -6, -113,
  0, 22, 29, 64, -288, -43, -200, 178, -11, 30, 63, -36, 9, -41, 79, 79, 63,
  129, 71, 269, 41, 86, 66, 49, 2, -219, -121, -207, 52, 209, 97, -187,
  -249, 29, 67, 27, -97, -140, -95, -112, 78, 51, 98, -21, 238, -149, 38,
  98, 64, 6, 98, -8, -10, 108, -70, 47, -71, 19, 98, 216, 157, 98, -4, 18,
  -53, -149, 179, -64, 87, -5, 119, 49, 131, 56, -48, -37, -121, 41, -31,
  54, 81, 89, -133, 9, -85, 82, 223, 104, 148, 168, 114, 116, -41, 181, -73,
  144, -57, 35, 106, -64, -43, -166, 32, -80, 159, -28, -75, 15, 44, 111,
  175, 97, 84, -157, 183, 27, 187, -9, 220, 66, 52, 90, 0, -45, 90, 95, -55,
  132, -140, 122, 35, -3, 30, 51, -29, 126, 37, -44, -52, -161, 118, -60,
  45, -43, -128, 38, -156, -64, -179, -158, -76, -153, 2, 27]

theorem fractionalNearFrameSubtreeG5R0105_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0105Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0105Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0105Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0105_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0105LowerBoundTable : List ℤ :=
  [68, 2, 311, 45, 161, 113, 353, 2, 93, 40, 530, 152, 1, 990, 699, 95, 550,
  391, -371, 542, 360, 395, 227, 53, 471]

def fractionalNearFrameSubtreeG5R0105LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0105Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0105LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
