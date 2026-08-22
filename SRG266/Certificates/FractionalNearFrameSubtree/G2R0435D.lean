import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0435`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0435Mask : ℕ := 5785395727506584

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0435Witness : Array ℤ :=
  #[397, 794, -722, 111, -581, 136, 470, -983, -331, -604, 915, 972, -180,
  333, -404, 246, -829, -77, -671, 784, 675, 208, 411, 686, 618, 73, 643,
  -62, -51, 197, -482, -657, 214, 963, 1042, -729, -907, -266, -476, 1270,
  -3, 719, 289, 855, 235, -850, -1623, -1463, 688, 655, -141, -814, -727,
  -819, 423, -40, 321, -307, 735, 84, 412, 35, 584, -172, 786, 280, 248,
  262, 836, 286, -207, 403, -620, -1, 287, -755, -73, -36, -820, -112, 835,
  416, -541, -123, 809, -288, -415, 426, -1012, -248, 549, 538, -508, 686,
  -31, -836, 99, -568, 833, 500, -109, 369, 846, 664, -188, -408, 445, -496,
  257, 551, -733, -413, -83, 473, -349, 392, 903, -362, 855, 587, -4, -14,
  267, 318, -320, -308, -84, 32, 530, -125, -43, -253, -259, 881, -223,
  -263, 899, -680, 340, -335, -143, -142, -850, 261, 223, -94, -190, 401,
  1529, 562, 123, 218, 658, -293, 158, -76, -653, -528, -1100, -182, -462,
  -694, -535, 76, 419, 46, 589, -167]

theorem fractionalNearFrameSubtreeG2R0435_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0435Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0435Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0435Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0435_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0435LowerBoundTable : List ℤ :=
  [-207, 33, 390, 241, 821, 129, 32, 146, 859, 415, 1328, -1035, 280, 522,
  2068, -333, 289, -748, 2390, 100, 1189, 284, 3974, 3228, 1738]

def fractionalNearFrameSubtreeG2R0435LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0435Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0435LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
