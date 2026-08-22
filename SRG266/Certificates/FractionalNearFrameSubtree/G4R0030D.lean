import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0030`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0030Mask : ℕ := 5369784576973073

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0030Witness : Array ℤ :=
  #[-328, -175, 88, -492, -84, 134, -579, 187, -106, 373, 442, 613, 141,
  -262, 169, -68, 106, -309, -43, -144, 168, -127, 148, -476, 100, 223,
  -194, 14, 45, 326, -134, 380, -412, 59, 250, 225, -711, -36, 992, 256, 76,
  -445, -246, 212, -139, -410, -362, 909, -617, -84, 559, 976, 147, 669, 0,
  89, -190, 488, 870, 107, -617, -112, -98, 470, -58, -69, 658, -83, 280,
  -334, 691, -418, -62, -130, 114, -402, 72, 165, -142, -104, 118, 446, 292,
  -186, 735, 27, 64, 59, 325, -585, -122, 248, 217, -185, 269, -488, -145,
  304, 146, -266, -72, -75, 94, 150, 215, 54, 124, -104, 492, 99, 57, -321,
  284, -35, 432, -556, -628, 151, 1014, -394, -39, 109, 159, -191, 0, 607,
  179, 0, 1203, 17, 444, 319, -440, 458, 186, 26, 823, -467, 360, -516,
  -315, 288, -656, 331, -255, -10, -713, 163, 92, 56, -97, 637, 667, -155,
  272, -64, -196, 524, -68, 38, -307, 201, -87, 206, -144, -218, 464, -240]

theorem fractionalNearFrameSubtreeG4R0030_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0030Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0030Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0030Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0030_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0030LowerBoundTable : List ℤ :=
  [377, 510, 1120, 935, 1, 1331, 248, -218, 837, 2227, -493, 1135, 1784,
  1142, 146, 976, 1613, 622, -943, 1018, 1172, 673, 540, 1453, -991]

def fractionalNearFrameSubtreeG4R0030LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0030Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0030LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
