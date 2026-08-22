import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0137`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0137Mask : ℕ := 1039265904902732

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0137Witness : Array ℤ :=
  #[1443, -431, -842, -1120, -626, 1276, -14, 873, -501, -1222, 1526, 1488,
  73, 722, 675, -874, -144, 83, -1023, 1394, 620, 1996, 837, -792, -400,
  -1103, 122, 1134, 1738, 1925, 1454, -636, -1364, -2164, 0, -675, 121,
  -1104, -960, 1266, -335, 1387, -777, -119, 951, -911, -646, 972, 199,
  2316, 1152, 337, 469, -1163, 614, 629, -237, 443, -216, 553, -604, 91,
  -273, 1988, 2721, -742, -629, -567, 912, 351, -20, -99, 965, 977, 1706,
  68, 416, -22, 217, 0, 621, -114, 145, -303, -603, -761, 379, -282, 455,
  1874, 396, -1587, 610, 704, 662, -452, 346, 1138, 1788, 709, 1233, 577,
  835, 1082, 401, -469, -32, 119, -907, 1013, 1499, 754, -391, -2038, 252,
  -192, 406, -1513, 381, 1208, 185, -93, 829, -332, -1793, -514, -738, -108,
  -595, -310, -1319, 55, 27, 182, 1601, 1106, -287, 64, -584, 1390, -158,
  481, 844, -299, 1224, 928, -1801, 913, -2443, 773, -130, 1710, -1242,
  -464, 281, 2083, -950, -1821, 874, -360, 595, -1232, -423, 147, -231,
  -709, -1360, 589]

theorem fractionalNearFrameSubtreeG1R0137_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0137Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0137Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0137Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0137_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0137LowerBoundTable : List ℤ :=
  [579, -689, 2755, 4778, 797, 3111, 1110, 32, 1810, 3053, -431, 32, -1979,
  4046, 1450, 1421, 4137, 6371, 3011, 3554, 4954, 2186, 2503, 1201, -2674]

def fractionalNearFrameSubtreeG1R0137LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0137Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0137LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
