import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0333`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0333Mask : ℕ := 5638206189579273

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0333Witness : Array ℤ :=
  #[2107, -847, -21, -191, -331, 87, -92, -506, -411, 0, -532, -690, 245, 0,
  -77, 181, 447, 128, -1084, 1759, -1275, -693, -395, -628, 0, -783, 129,
  -771, 401, 648, 994, 1143, 514, -1319, 79, -880, -92, 43, -974, -102, 812,
  555, 874, 380, -81, 836, 2020, 466, 1009, 1055, -2216, -1143, -1535,
  -2218, -689, -1596, -920, -418, -596, -1646, -647, 2561, 469, 524, 107,
  270, -39, 289, 0, 823, -198, -700, 1007, -684, 556, 313, -78, 56, 577,
  373, -881, -297, 1029, 804, -150, 510, 133, -513, 369, 19, -90, -981, 247,
  -368, 618, 43, 575, -147, 674, -871, 50, -969, -316, 369, -612, 256, -819,
  -752, 241, -823, 430, -818, 391, 1540, 664, 1347, 996, -358, -928, 0,
  -462, 1, 601, -1559, -945, -646, 785, -594, 533, -832, 467, 87, 372, 315,
  -983, -282, -266, 32, -597, -1050, 251, 656, -1488, 1046, 825, -293, 1176,
  265, 900, -427, 538, -331, 916, -150, -654, -39, 321, -274, 678, 259,
  -260, -614, 111, -109, -10, -983, 284, -439]

theorem fractionalNearFrameSubtreeG2R0333_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0333Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0333Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0333Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0333_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0333LowerBoundTable : List ℤ :=
  [-1584, -544, -1605, 585, 298, -1349, 32, -64, 32, 4317, -1407, 1227,
  -1210, 3000, -2795, -3198, -415, -547, -1619, 2169, 2157, -372, 638,
  -2670, -667]

def fractionalNearFrameSubtreeG2R0333LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0333Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0333LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
