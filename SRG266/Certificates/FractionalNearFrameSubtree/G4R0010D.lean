import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0010`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0010Mask : ℕ := 4738668174330117

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0010Witness : Array ℤ :=
  #[1926, 1005, 1528, 158, -312, 908, -2775, -1269, 0, -2570, -2517, 2412,
  1470, 1102, 938, 710, -364, -818, 381, -459, 295, 968, 3192, -497, -862,
  -86, -881, 968, 265, 0, -637, 778, 1530, 533, 78, -330, -1160, -2409,
  2464, 1617, 1439, 477, -1467, 916, 544, 827, -223, -807, -70, -357, -404,
  -167, -1393, -639, 1751, 1396, -708, -565, 678, 1183, 493, -2704, -921,
  -356, 150, -190, 903, 636, -181, 1019, 118, 310, 1485, 305, 447, 392,
  -771, -1477, 76, 668, 331, -555, 58, -79, 1461, -171, -242, -1919, -575,
  -219, 1268, -403, 969, 843, 1086, -502, -191, -952, -281, 775, 565, 659,
  -612, 427, 714, 1627, -380, -1201, 678, -872, 611, 1216, -245, 582, 1185,
  3245, -289, -729, -1500, -1037, 79, 51, 1752, -686, -1249, 355, -350, 544,
  1130, 279, 92, -944, 1590, -208, 322, 430, 1942, -1251, 1107, -1743, 191,
  -694, 1262, 589, -173, -200, 30, 1361, 1735, -138, 1419, -927, 1321, 807,
  340, -391, 1684, -2863, -1460, -61, -231, -1422, -455, 441, -1384, -173,
  936, 295]

theorem fractionalNearFrameSubtreeG4R0010_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0010Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0010Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0010Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0010_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0010LowerBoundTable : List ℤ :=
  [330, 916, 32, 466, 1639, 406, 1895, 2103, 1841, 1707, 1315, 4703, 1020,
  4609, 100, 5148, 5276, 1504, -1309, 3659, -4895, 3869, 3023, 1098, 4411]

def fractionalNearFrameSubtreeG4R0010LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0010Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0010LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
