import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0199`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0199Mask : ℕ := 6874407220456984

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0199Witness : Array ℤ :=
  #[73, 53, 373, 2226, -2484, 368, -1646, -1914, -316, -580, 420, 5332, 699,
  321, 62, -1294, 153, -1692, 704, 1213, 1161, 423, 1046, -790, -780, -823,
  -1896, -704, -2055, 669, 936, 2987, -1050, 0, -1068, -918, 1712, 1397,
  1310, -1839, 1088, -318, 101, -144, -2037, 1030, -400, 1105, 846, 1294,
  412, 88, -290, 963, 4328, 1445, 2025, 2430, 308, 1688, -971, 2279, -896,
  3067, 761, 3948, 1334, 959, -1226, -1675, -737, -673, 325, -1052, -1345,
  0, 588, -825, 708, -1304, 858, -376, 280, 278, 3731, 1089, -1568, 254,
  -1861, -1185, 4458, -386, 2890, 226, 3599, -1600, -721, -1159, -1883, 674,
  2017, 841, 1048, 452, -579, 2513, -1867, 1196, 722, -4479, -1230, 1140,
  3008, -893, 3445, -2913, -30, 3011, -2602, -383, 499, -1101, -111, 177,
  1029, 4631, 2720, -4, 1345, 620, 338, 3516, 134, 2589, -516, 1028, -214,
  -1615, -67, 595, -1488, 662, -1423, 4343, 1753, 1841, 1373, 0, -571, 2,
  545, -604, 240, 1592, 1362, 3212, 1390, 1763, -751, -2717, 3385, -1100,
  -380, 1980, 0, 1947, 1446, 1413]

theorem fractionalNearFrameSubtreeG3R0199_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0199Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0199Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0199Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0199_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0199LowerBoundTable : List ℤ :=
  [2945, 6926, 8771, 3969, 32, 4232, 4824, 3165, 4538, 6001, 6466, 18162,
  3750, 8835, 7163, 8210, 8454, -1585, 6293, 2592, 2815, 10343, 100, -3171,
  9442]

def fractionalNearFrameSubtreeG3R0199LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0199Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0199LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
