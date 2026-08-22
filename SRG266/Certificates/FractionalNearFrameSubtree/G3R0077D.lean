import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0077`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0077Mask : ℕ := 2361472022717443

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0077Witness : Array ℤ :=
  #[2299, -1868, -326, -266, 0, -799, 38, 524, -1877, -3070, 0, -408, 2422,
  3179, 3309, 2476, 1464, 4263, 1149, -247, -274, 1334, 427, 738, 3004,
  1518, 0, 2553, 3515, -1414, -1821, 1471, -4340, -1444, 3144, 365, -509,
  307, -325, 1685, 1279, 2641, -969, 248, 294, -1322, -2811, 2812, 2639,
  1596, 0, 122, -536, -691, -1523, -1192, -2094, 709, -1695, -1461, -2461,
  -1655, -1297, -484, 464, -993, -419, 580, 1509, -893, -713, 1050, 970,
  1154, 838, -432, 1880, 378, 410, 1236, 2107, -866, -1103, 58, 139, -755,
  629, 838, -69, -249, -3492, -849, -1523, -635, 348, -1691, 1041, -308,
  734, -272, 1307, -972, 178, 528, -263, 4, 403, 641, 525, 863, -3057, 1665,
  1439, 1051, 1171, 749, 654, -1730, -942, 3391, -1256, 598, 580, 218, 2366,
  -800, 1525, 1956, 16, 1267, 1655, 2532, -1733, 1303, -2679, 533, 591, 866,
  1659, 537, 925, -1090, 1030, 927, 2226, 1533, 3269, 3402, 621, 782, 371,
  110, 752, -1845, 1071, -868, 306, 1556, 8, -321, 589, -2541, -3773, -237,
  221, 1911, 3427, -70]

theorem fractionalNearFrameSubtreeG3R0077_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0077Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0077Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0077Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0077_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0077LowerBoundTable : List ℤ :=
  [2096, 5133, 31, 91, 4109, 5278, 6859, 4183, 2314, 7112, 10654, 3072,
  11249, 6359, 262, -48, -2490, -187, 1646, 11, 167, 4520, 3947, 13126, 99]

def fractionalNearFrameSubtreeG3R0077LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0077Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0077LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
