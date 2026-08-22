import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0548`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0548Mask : ℕ := 6839739497517706

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0548Witness : Array ℤ :=
  #[-654, 1006, -25, 664, 2514, 1950, -311, 558, 231, -663, 13, -2303, -544,
  178, 400, -1615, -713, 660, -246, -202, 952, 376, 440, 39, 202, -124, 637,
  341, 0, 227, -54, -137, 1096, 510, -642, 388, 770, -280, -486, 802, 563,
  1180, 1135, -469, 576, 583, -311, -945, 944, 323, 861, 359, -767, -199,
  717, 218, 1114, 727, 56, -373, 179, 355, 434, -449, -1257, -126, 659, 177,
  535, 773, 1587, -526, 531, 832, 52, -698, 437, 1405, 1114, 215, 469,
  -1012, 706, 849, 511, 1119, 755, -64, 692, 120, 239, -1002, 540, -5, -629,
  374, 296, -601, 458, -65, 413, 2, 226, -1034, -1355, -428, -664, -343,
  -256, -279, 208, 54, 1278, 466, -151, -57, -34, -1280, -276, 131, 1487,
  433, -851, 84, 199, 408, -42, 1093, 336, 665, -19, -1031, -18, 508, 577,
  684, -387, -243, -430, -191, 308, -385, 743, -382, 1423, 666, -15, 882,
  -106, -308, 1550, 427, 1288, -283, 945, -114, -875, 1518, 520, 1076, 724,
  -553, 1331, -10, 257, 679, -884, 71]

theorem fractionalNearFrameSubtreeG2R0548_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0548Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0548Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0548Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0548_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0548LowerBoundTable : List ℤ :=
  [2087, 2869, 1878, 3380, 1877, 3126, 348, 382, 1529, 2124, 2500, 100,
  2447, 100, 1968, 1742, 7197, 1525, 2265, 8830, 3191, 2721, 1492, 4298,
  5438]

def fractionalNearFrameSubtreeG2R0548LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0548Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0548LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
