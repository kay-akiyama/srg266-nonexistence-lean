import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0062`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0062Mask : ℕ := 953996545729674

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0062Witness : Array ℤ :=
  #[336, -380, 81, 208, -884, 78, 75, 150, 0, 357, 421, 330, 396, 224, 174,
  -575, 994, 441, 387, 371, 700, 35, 193, -189, -84, 136, -746, 163, -315,
  -960, 1079, -232, 427, 615, 935, -536, -1052, 1111, -582, -559, -1182,
  -601, 99, -749, -1208, 373, 390, 625, -14, 944, 612, -381, -784, -472,
  251, -819, -86, -231, 709, 701, -1291, 603, 34, 112, 204, -406, 541, 558,
  -519, -214, 550, -264, 75, 378, -6, 238, -935, -192, 237, 335, 145, -269,
  473, 673, 979, -601, -202, 258, 501, 142, 951, 401, 672, -1040, 478, 74,
  -787, 149, -503, 352, -623, -110, -335, -1270, 596, -289, -4, -151, 499,
  144, 113, 29, -242, 103, -893, 111, 230, 276, -159, -407, -13, -1, 1167,
  -93, 288, -134, -6, -454, 1181, -919, 195, -583, 1608, 213, 896, 212,
  -240, -118, -524, 1016, -1520, 25, -57, 340, 584, -328, -182, 177, -301,
  -580, -577, -654, -271, -606, 464, -349, -120, 23, -365, -172, -54, 230,
  237, 835, 466, -556, 990, -130]

theorem fractionalNearFrameSubtreeG2R0062_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0062Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0062Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0062Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0062_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0062LowerBoundTable : List ℤ :=
  [-700, 32, 32, 827, 280, -519, 51, 32, 425, -972, 3071, 184, -2353, 1781,
  -290, -168, 4042, 1324, -1275, -219, 99, 100, 2956, 1277, 1339]

def fractionalNearFrameSubtreeG2R0062LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0062Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0062LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
