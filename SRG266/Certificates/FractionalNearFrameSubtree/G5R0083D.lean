import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0083`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0083Mask : ℕ := 5471533637796178

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0083Witness : Array ℤ :=
  #[743, 368, 343, 618, 947, -130, -648, -448, -669, -885, 137, -1080, -803,
  99, 0, -527, -682, -734, 347, 693, -345, 1, -1187, -693, -337, -159, 256,
  -160, 293, 1227, -748, -796, -340, -11, -1452, 126, 1359, 748, -775, 65,
  2426, 1282, -952, -1147, -1652, -391, 217, -463, -968, -1529, 2556, -1117,
  -1695, -296, 1204, 1246, 205, -677, -39, 76, 30, 247, 255, -303, 283, 648,
  -13, 193, 7, 758, -581, -526, 913, 980, 98, -1460, 80, 300, -410, 686,
  -446, 699, 575, -248, 776, 755, 249, 921, -904, 378, 371, 1148, -252, 616,
  756, 587, 1282, 472, 225, -316, 860, 244, 204, 639, 566, -5, 495, -58,
  1136, 441, -15, 914, -301, -58, -450, -19, -484, -204, 537, 878, -270, 75,
  691, 290, 228, 437, -381, 27, 537, -126, 278, 70, -1310, -337, 1321, 815,
  0, 221, -142, -1352, 388, 1536, 1244, 184, 193, 1063, 275, 228, 120, 785,
  -764, 651, 1006, -1028, 1044, -37, -250, -1, 290, -710, 296, 119, -273,
  844, -855, -310, -916, 404]

theorem fractionalNearFrameSubtreeG5R0083_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0083Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0083Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0083Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0083_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0083LowerBoundTable : List ℤ :=
  [6, 1970, 33, 2245, 948, 163, 1529, 1039, -431, 789, 6009, 1593, 1954,
  4063, 676, 1445, -2053, 100, 1920, 1620, 100, -339, 882, 6742, -1066]

def fractionalNearFrameSubtreeG5R0083LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0083Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0083LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
