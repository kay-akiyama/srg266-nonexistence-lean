import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0073`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0073Mask : ℕ := 962643673944280

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0073Witness : Array ℤ :=
  #[910, -626, 81, 787, -381, 827, 578, 996, 1005, 64, -611, -1684, -757, 0,
  80, -465, 519, 692, -230, -112, -551, -169, 30, -678, 714, -746, 69, 503,
  562, -180, 675, -227, 558, -720, -861, 434, 284, 1726, 85, -758, -1509,
  -1238, -2, -611, -440, -51, -706, 932, 932, -633, 215, 33, 984, 1008, 394,
  98, -141, 584, 364, 681, -494, 350, 711, -943, -993, -445, 340, -220, 215,
  569, -380, -1134, 192, 367, -623, 242, 278, 3, 200, -567, -971, 735, 474,
  1080, -737, 384, 58, -573, -171, 386, 41, 60, 0, -74, 517, 347, -369, -2,
  751, -323, 181, 672, -134, 110, -278, 228, -655, 452, -730, -772, 633,
  156, 247, -798, -285, 202, 446, -727, -543, -706, 849, 388, 252, 6, 463,
  -381, -142, -1600, 530, -431, 82, -540, 866, -74, 246, 17, -1376, 1077,
  -307, -403, 147, -286, -164, -180, 240, -115, -106, 25, 62, 424, 687,
  -222, 1284, -1074, -592, 1157, 999, 73, 279, 982, 830, -307, 251, 258,
  -384, 223, 8, -1192]

theorem fractionalNearFrameSubtreeG2R0073_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0073Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0073Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0073Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0073_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0073LowerBoundTable : List ℤ :=
  [-507, 32, 32, 264, -293, 1413, -593, 534, 156, 3846, -1293, -166, -1455,
  1976, 99, -866, 296, 7, 1792, 3072, 1464, 635, -3060, -115, 2587]

def fractionalNearFrameSubtreeG2R0073LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0073Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0073LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
