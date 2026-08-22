import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0474`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0474Mask : ℕ := 5809430498516120

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0474Witness : Array ℤ :=
  #[-969, -1347, -815, 55, -1326, 1633, 1155, 1077, 491, -659, 1396, 751,
  1451, 341, 1604, 1011, 674, 393, 1967, 1348, -269, -809, -55, -129, -737,
  -964, -1628, -974, 326, 1358, 600, 302, 1038, -527, -130, 1238, 386, 646,
  114, -1558, 290, -144, 1420, 240, 706, -641, 401, 32, -133, 280, 283,
  -991, -192, 228, 206, -214, 1307, 1019, 762, -169, 231, 302, 595, 1295,
  -1329, 615, 153, 1014, 19, 63, 1111, -85, 648, -362, 954, 212, 1614, 174,
  414, 1221, -643, 164, -1417, -1023, -1670, -930, -784, 707, -140, -399,
  -808, 274, -722, 378, 247, 248, -873, 391, 1359, -964, -626, 336, -54,
  316, 101, -1629, 547, -162, -661, -694, 35, 285, -576, -364, -215, -990,
  -1319, -1655, -1554, 807, -632, 672, -293, 928, -566, -1343, -3, -425,
  -744, -60, 177, 467, 760, 270, -421, -1080, 1597, 629, 180, 82, 1248, 437,
  1157, 226, -697, 306, 530, -262, -851, 1186, -731, 777, 413, 744, 933,
  716, -79, -96, -226, 305, 99, -203, 479, -142, -1443, 952, 795, 312]

theorem fractionalNearFrameSubtreeG2R0474_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0474Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0474Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0474Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0474_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0474LowerBoundTable : List ℤ :=
  [-384, -230, 32, 925, 32, 607, 32, 2042, 3118, -1115, -1106, 1976, 100,
  2247, 2069, 587, 6350, 2202, -87, 5979, 100, 730, 1602, 3160, 2483]

def fractionalNearFrameSubtreeG2R0474LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0474Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0474LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
