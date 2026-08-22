import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0232`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0232Mask : ℕ := 2909964520620642

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0232Witness : Array ℤ :=
  #[734, 962, 1036, 443, 64, 338, 255, 0, 59, 163, 126, -137, -747, -418,
  224, -2027, -219, 509, -118, -601, -1421, 541, 292, 142, -686, -353, 730,
  -27, 0, 1652, 266, 107, -720, -860, -436, -130, -195, 339, 146, 489, -50,
  871, 107, 1509, -1438, 1067, 285, -443, -386, -996, -1000, -382, 30, -609,
  745, 703, 423, 275, 1000, -986, -1453, -1542, -1040, 285, 131, -489, -389,
  -76, -667, 191, -317, 695, 405, 325, -1774, 251, 339, 488, 125, -92, 256,
  -906, -618, 536, 1659, -408, 385, 20, 110, 939, 1008, 1982, 906, -74, 774,
  -325, -355, 429, -37, 1529, 540, 510, -165, -1330, 1737, 135, 679, 1676,
  -431, -345, -208, -84, 27, -1566, -68, 151, 326, 175, -276, 107, 914,
  -125, 68, 40, 351, 383, -381, -525, -1508, 36, 216, 952, 119, -1183, 490,
  650, 437, 392, -241, 552, 185, -1494, 855, 404, 359, -152, -256, -10,
  -364, -12, -785, -830, 1034, 1314, -1354, 691, 73, 862, 1767, -894, 471,
  261, 423, 1434, -289, -1775, 0, -1069]

theorem fractionalNearFrameSubtreeG2R0232_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0232Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0232Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0232Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0232_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0232LowerBoundTable : List ℤ :=
  [-691, 32, 708, 153, 258, 32, 33, 505, 840, -2731, 2340, 1426, 1133, 4359,
  724, 228, 2307, 3164, 2057, 2301, 2823, 100, 817, 1388, 100]

def fractionalNearFrameSubtreeG2R0232LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0232Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0232LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
