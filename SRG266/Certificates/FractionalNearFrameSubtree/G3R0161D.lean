import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0161`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0161Mask : ℕ := 6850834909764016

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0161Witness : Array ℤ :=
  #[-321, 1294, -1083, -274, -853, 300, -775, -105, -507, -200, 969, 504,
  484, 547, -371, 875, 362, 607, 275, 528, 502, 449, 591, 530, -819, -736,
  -1491, -879, 178, -1000, -573, 98, -98, 968, 332, 115, -108, 282, 715,
  1082, 741, 1222, 917, -219, 510, -1506, -944, -769, 292, -548, 692, -787,
  -663, -1613, -301, -212, 42, 745, 641, -690, 236, -477, 1006, -403, 992,
  762, 385, -108, 355, -322, -455, -163, 475, -790, 398, -1324, -1266, 532,
  -660, 565, -147, 285, -468, -452, 1420, 339, 283, 296, 821, 639, -14, 356,
  129, -650, 780, -330, -97, -571, 1211, -361, 683, -480, -60, -368, 281,
  172, -428, 177, 557, -178, 0, -226, 437, -800, 50, 142, -468, 225, 548,
  1492, -321, -428, -551, -263, -513, 324, 22, 811, 152, 922, -278, 225,
  -86, -635, 590, -992, 66, -488, -54, 9, -111, -217, 950, 351, -260, 2,
  223, 148, 191, -659, 330, 299, 1007, -559, -447, 590, -123, 1355, -219,
  -186, -63, -41, 1001, -242, -561, -522, 138, -154]

theorem fractionalNearFrameSubtreeG3R0161_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0161Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0161Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0161Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0161_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0161LowerBoundTable : List ℤ :=
  [-354, 478, 31, 844, 112, 479, 33, 216, 141, 1730, 1827, -278, -1346, 847,
  -930, 1876, -2035, 406, 2384, 4633, 771, 2936, -680, 1300, 102]

def fractionalNearFrameSubtreeG3R0161LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0161Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0161LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
