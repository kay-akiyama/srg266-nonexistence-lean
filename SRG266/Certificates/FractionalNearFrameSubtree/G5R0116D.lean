import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0116`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0116Mask : ℕ := 5794190552041569

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0116Witness : Array ℤ :=
  #[1774, 777, 633, 714, 706, 26, 263, 709, -199, 781, -301, -1050, -637,
  -850, -870, -95, 183, 1489, 1833, 699, 753, -1105, -915, -147, 381, -147,
  1370, 0, 108, 1151, 99, -364, -330, 121, -710, 47, -504, 160, 736, 122,
  613, 74, 1027, -815, 760, 129, 1124, 1639, -785, -973, 362, -1006, -724,
  -481, 950, -1041, -1442, -1328, 1031, -21, -244, -3, 432, 265, -731, -379,
  -1151, 302, -38, 205, 46, 312, 91, -585, 361, 943, -380, -204, -536, -452,
  -701, 682, 265, -566, -16, 1932, 692, -527, -645, 1354, 317, -719, 247,
  111, 457, -201, 172, 1304, 202, -262, 1831, 162, -65, -710, -355, -3,
  -336, -157, -557, -1252, 533, 1359, 706, 598, 812, 13, -844, -329, -88,
  1106, 818, 379, 250, 75, 267, 299, -104, -710, 386, 506, 202, 67, -93,
  261, -1228, -732, 1136, 598, 1016, -163, 970, -176, -647, 420, 2, -1123,
  52, 1456, 94, -294, 822, 788, 150, 437, 273, 848, 356, 436, -747, -642,
  -248, 551, 1428, 0, 113, 257, -1791, -565]

theorem fractionalNearFrameSubtreeG5R0116_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0116Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0116Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0116Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0116_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0116LowerBoundTable : List ℤ :=
  [444, 1247, 32, 32, 32, 2467, 2677, 2883, 32, 2451, 5407, 101, 654, 99,
  663, 2187, -1663, 1158, 6013, -838, -570, 1993, 1882, 5221, 1449]

def fractionalNearFrameSubtreeG5R0116LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0116Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0116LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
