import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0568`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0568Mask : ℕ := 6846483505845522

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0568Witness : Array ℤ :=
  #[-1300, 984, -683, 932, 596, 776, -1279, -202, -13, 8, 254, -290, -330,
  -63, 532, -698, -1652, -557, -1277, -961, -1221, -745, 558, -1413, -351,
  -593, 496, 2212, 2177, 2212, 176, -302, 1036, -784, -1452, 866, 529, 488,
  86, -291, -42, -282, 990, 1916, 1189, 52, 829, 0, -74, -896, -2156, -515,
  789, 1173, -3, -337, -660, 829, 1015, -133, -234, -42, 104, 107, 428,
  1746, -187, -697, 359, 1115, 131, 1087, 1084, 439, -434, 331, 808, 569,
  -744, 551, -644, 930, -371, 905, -625, -134, 502, 545, 948, 984, -925,
  1400, 350, 514, -1297, -339, 73, -1388, -689, 487, 65, 323, -296, 324, 62,
  -514, 140, 249, -1221, 1449, -328, -1196, 320, 638, 202, 406, -237, -928,
  392, -210, -724, 1141, 284, 1072, -935, -962, -593, 796, -689, 580, 307,
  904, 524, 1105, 1059, 877, 477, -440, -99, -68, 1314, -225, 862, -631,
  246, 19, -526, 758, 1476, -107, 1692, -52, -574, -970, -1119, -506, -181,
  -80, -394, 66, -1434, -231, 837, -330, 1281, -420, -1236, 244]

theorem fractionalNearFrameSubtreeG2R0568_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0568Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0568Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0568Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0568_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0568LowerBoundTable : List ℤ :=
  [-34, 1366, 1461, 1335, -1053, 1016, 452, 1040, 322, 1303, 2626, 99,
  -1325, -218, 2879, 6239, 101, 2163, 3140, 3487, 5719, -3411, 98, 2160,
  1555]

def fractionalNearFrameSubtreeG2R0568LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0568Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0568LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
