import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0222`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0222Mask : ℕ := 2479979232859220

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0222Witness : Array ℤ :=
  #[464, 54, 0, -519, -11, -877, 384, -264, 981, 497, -1406, 93, 491, -687,
  -97, -223, -977, -200, -1665, -363, -1166, -84, -223, 909, -621, 264, 701,
  793, 603, 305, -177, 22, -30, 545, -264, 564, 1572, -1781, -1605, 458,
  -2209, 328, 309, 840, 546, 303, 297, 43, 266, 110, -574, -135, -1138,
  -868, -454, 59, -586, 141, 119, 621, -96, -391, 781, 773, -858, -153, 358,
  156, 20, 416, -185, -291, -302, 329, 379, -805, -540, -1358, 765, -1219,
  -88, 761, 552, -330, 109, -184, 406, 219, -197, 1216, 593, -425, 85, 163,
  637, -1201, 49, 220, -1238, 138, 916, 729, -1252, 311, 182, -1747, 135,
  -185, -1072, -928, 1201, -353, 547, 533, 358, 138, 937, -343, 177, -443,
  917, 1107, -738, -1226, -1071, 223, 155, -174, 499, 423, 956, -2345, -55,
  -496, 0, 461, 461, 951, 540, 401, 361, 2403, 778, -316, -631, -971, 968,
  77, 433, 464, -207, 1033, -1639, -1579, -1327, 144, 0, -774, -450, -21,
  1435, -94, 0, -1315, -39, 247, 257, 64]

theorem fractionalNearFrameSubtreeG2R0222_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0222Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0222Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0222Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0222_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0222LowerBoundTable : List ℤ :=
  [-1470, 61, 12, -550, 462, 31, -231, -1140, -2898, 379, -1408, -1700,
  1004, 1432, 1540, 1912, -5175, -1238, 97, 2259, -2176, 98, 2203, 2043, 73]

def fractionalNearFrameSubtreeG2R0222LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0222Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0222LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
