import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0138`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0138Mask : ℕ := 1039396767383892

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0138Witness : Array ℤ :=
  #[1089, 74, 339, 311, 36, -193, 1279, 3130, -1603, -944, 193, -595, 167,
  93, 1109, 427, -125, 180, 17, 231, 3593, -1430, 734, -451, -349, -4, 208,
  -894, 791, 1369, -587, 1133, 621, 1046, -3120, -2510, -868, 617, 3422,
  -2030, -852, 0, -572, 250, -270, -444, -485, -3889, 439, 1361, -87, -411,
  1237, 781, 476, -594, 978, -2073, 874, -361, 419, 238, 750, -1171, 701,
  431, -3548, 117, -424, -213, -575, 690, 7, 694, -1048, 30, 1736, 249,
  2385, 1871, 316, 1011, 748, 69, -1668, -134, -3837, 2347, -563, 71, 220,
  670, 424, 631, -607, 498, 1202, 2755, -593, 1054, 755, 942, -1398, 288,
  -2199, 4176, -1179, -332, 140, 807, -100, 360, 992, -736, 2578, -650,
  -1040, 689, -183, -1796, 462, 3809, -2332, 239, -2353, -3662, 1719, -29,
  -780, -1711, -2491, -706, 2022, 2984, -468, 1428, -257, -957, 814, -500,
  1036, -1250, 1358, 105, -843, -1012, 1555, 708, 916, -750, 38, 1011, 490,
  2755, 592, -319, 1038, 1043, 54, 1600, -430, 1680, 271, -544, -1433, -29,
  -3202, 1372]

theorem fractionalNearFrameSubtreeG1R0138_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0138Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0138Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0138Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0138_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0138LowerBoundTable : List ℤ :=
  [381, 1266, 2157, 1275, 210, 32, 4056, -3314, 2277, 200, 4008, -3897,
  6436, -480, 10774, -326, 2125, 2261, -1353, -2498, 5939, 1962, -500, 3751,
  3053]

def fractionalNearFrameSubtreeG1R0138LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0138Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0138LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
