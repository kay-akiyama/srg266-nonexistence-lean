import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0308`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0308Mask : ℕ := 5387249024413208

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0308Witness : Array ℤ :=
  #[-26, -142, 0, 377, 99, -61, 65, -190, 140, 205, 63, 507, 278, 322, 48,
  -146, 247, 318, -142, -222, 357, 87, -195, 27, 52, 232, 317, 576, -262,
  54, 426, -73, -526, 519, -194, 360, -285, -433, 112, 230, 873, -241, 582,
  222, 237, 234, -263, -469, -223, 169, 89, 462, -345, -147, -32, -551, 515,
  47, 581, 700, -328, 34, 111, 420, 275, 374, 911, 191, 165, 161, 80, -244,
  -63, -126, -264, -306, 0, -227, 208, -267, -40, 253, 42, 144, 211, 28,
  370, -760, -210, 124, -569, -453, 99, -138, 125, 210, -122, 102, 84, -271,
  312, 400, 177, 344, 32, 133, 24, 326, 297, 357, 39, 266, -180, -118, 141,
  155, -212, 60, 554, 532, 259, -21, -164, -223, 237, 283, 226, 238, 97,
  -182, 34, 553, 265, 483, 11, 317, -156, 334, -450, 400, 442, 173, 174, 22,
  383, -16, 89, -74, -120, 54, 182, -307, -628, 175, -324, 30, -27, -202,
  -464, 184, -249, 218, -181, 267, 22, 219, -61, -37]

theorem fractionalNearFrameSubtreeG2R0308_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0308Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0308Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0308Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0308_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0308LowerBoundTable : List ℤ :=
  [786, 764, 699, 1127, 745, 655, 134, 173, 1271, 1020, 1251, 1722, -24,
  1482, 521, 1139, 1205, 231, 1361, -216, 2390, 586, 3082, 706, 762]

def fractionalNearFrameSubtreeG2R0308LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0308Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0308LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
