import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0269`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0269Mask : ℕ := 5369792212210776

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0269Witness : Array ℤ :=
  #[243, 394, 191, 1150, -200, -588, 10, 2044, 662, 214, -424, -641, -1191,
  -80, -401, -695, -953, 660, -326, -1890, 1792, 855, 479, -120, 589, 791,
  987, 984, 205, 625, 630, 862, -1875, -1106, -2407, 736, 859, -1571, -1420,
  -156, 311, 930, 374, 732, 15, 864, -393, -1088, 2, -231, 930, -90, -263,
  -1067, 142, -154, -311, -3451, 292, 938, 90, -100, 843, 1577, -1481, 1802,
  78, -771, 777, 347, -71, 304, -645, 249, -292, -424, -687, 535, -294, 613,
  -220, 1094, 1759, 793, 758, -572, 30, 436, 139, -765, -118, -84, -233,
  -622, -495, -816, 1283, 1284, 534, 197, -463, 1229, 851, -260, -51, 1077,
  404, -239, 632, 1780, 1793, -1228, 1620, 713, 212, 681, -16, 536, 579,
  148, -673, 2196, 2067, -2617, -2164, 1015, 1299, -2439, 1207, 11, -437,
  -224, 1058, -547, -856, 1947, 706, 856, 790, 211, 772, -170, 68, 645, -61,
  788, 335, 542, 115, 1133, 503, -679, 387, -246, -134, -611, -668, 1300,
  1302, -523, -753, 1996, 363, -352, -734, -654, 0, 671]

theorem fractionalNearFrameSubtreeG2R0269_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0269Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0269Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0269Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0269_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0269LowerBoundTable : List ℤ :=
  [883, 3137, 2442, 3318, 354, 2430, 32, 1244, -914, 3693, 4752, 4723, 3556,
  99, 3369, 100, 847, 2508, 2088, 743, 4860, 100, 1877, 1056, 1318]

def fractionalNearFrameSubtreeG2R0269LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0269Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0269LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
