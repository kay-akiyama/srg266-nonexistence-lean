import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0031`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0031Mask : ℕ := 506792746198150

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0031Witness : Array ℤ :=
  #[-2695, -1005, -2022, -468, -2231, -2166, 787, 610, 401, 628, 1128, 774,
  233, -210, 626, 309, -687, 1771, 704, -1478, -37, -853, -615, 1059, 823,
  -228, 440, -228, 681, -159, -202, -871, -1279, -504, -1780, -1474, -639,
  -475, 1111, 738, -226, -460, 1565, -1241, 1130, 1889, 2758, 378, 772,
  1046, -1093, -499, 1537, -704, -508, -528, -931, -1532, 583, 304, -537,
  -1177, -836, -935, -315, -84, 892, 200, 886, 1978, 100, -114, -227, -313,
  559, 380, 146, 786, 128, 1579, 247, 1126, 123, 994, 393, -93, -313, 182,
  -941, 97, 1968, 530, 275, 867, -138, 2148, 147, 456, -327, 326, 1361, 96,
  -497, 1350, -679, 1724, 662, 874, -1252, -911, 907, 232, -241, -350,
  -1750, 67, -714, 177, 835, 436, 246, -1337, -282, -2122, -1435, -763,
  -470, 4136, -964, -1630, -89, 472, -977, 1601, 298, -619, 1180, 284, -374,
  1109, -142, -589, -42, -1294, 698, 985, -252, -1637, 268, -834, 1243,
  1613, 293, -1571, -1374, -598, 295, -999, 64, 199, -261, -621, -751,
  -3063, -429, 842, 474, 733]

theorem fractionalNearFrameSubtreeG1R0031_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0031Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0031Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0031Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0031_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0031LowerBoundTable : List ℤ :=
  [-705, 31, 703, -1675, 1973, 31, 32, -302, 31, 1591, -1299, -3921, 83,
  994, 2545, 3228, 99, 685, -4804, -2523, 2110, 1769, 101, 1635, -812]

def fractionalNearFrameSubtreeG1R0031LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0031Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0031LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
