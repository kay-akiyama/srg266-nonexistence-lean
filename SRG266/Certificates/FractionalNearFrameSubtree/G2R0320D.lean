import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0320`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0320Mask : ℕ := 5389585020998320

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0320Witness : Array ℤ :=
  #[1069, 315, 806, 746, 432, 684, -1743, 1358, 233, -408, -895, -912, -943,
  -1111, 576, 727, -1076, 177, -871, 1319, -1150, -372, 0, -39, 120, 220,
  1240, 0, 168, 970, -35, 1482, -662, 1058, 1040, 330, -423, -1310, 565,
  -730, -882, 15, 1488, 682, 1448, 822, -743, -1082, 218, -183, 6, -1766,
  -689, 72, -848, 1975, 169, 516, -148, 300, 195, 1397, -183, -98, 373,
  -685, 217, -598, -615, 764, 881, 413, 1277, 1127, 1319, -1261, -80, 5,
  643, 163, -981, -746, -676, 382, -382, 647, 1778, 829, -340, 723, 341,
  2099, -72, 389, 857, -1633, -637, 726, -1584, -500, 275, 682, 441, 373,
  582, 1222, -134, 1112, -1719, -211, -1391, -998, -104, 1194, -1239, -694,
  696, 477, -668, 1188, 1027, 973, 2161, 1167, 1563, -309, 746, 228, -608,
  358, -93, 1696, 732, 223, 157, 1583, 910, -551, 540, 387, 32, -806, -789,
  1058, -1021, 195, 985, -61, 1040, 417, -730, 260, -162, -276, 649, 2196,
  372, -456, 1197, -1445, 1166, -1191, 796, 0, 308, 552, 3154, 904]

theorem fractionalNearFrameSubtreeG2R0320_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0320Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0320Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0320Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0320_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0320LowerBoundTable : List ℤ :=
  [1517, 4562, 2123, 2345, -1367, 825, 5232, 2467, 2221, 3451, 7467, 1879,
  3877, 3362, 6312, 517, 1916, -103, 2017, -2477, 1593, 2032, 1903, 3581,
  4790]

def fractionalNearFrameSubtreeG2R0320LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0320Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0320LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
