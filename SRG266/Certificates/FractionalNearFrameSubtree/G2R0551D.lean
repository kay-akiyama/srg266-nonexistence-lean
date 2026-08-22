import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0551`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0551Mask : ℕ := 6839879998215314

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0551Witness : Array ℤ :=
  #[33, 1274, -1134, -18, 79, 985, -2200, 1447, -149, 299, -2469, -435, 0,
  206, -514, -1151, 514, -44, 1168, -1262, -1322, -1598, 505, -1764, -756,
  -1463, 1620, 2472, 370, 1409, -140, 242, 2851, -3046, 289, -250, 1246,
  558, -41, -3013, -1150, 0, -133, -198, -862, -1974, 1763, 346, -1427, 50,
  46, 1517, -2042, -1237, 253, 1286, 2771, -530, -393, -1711, -1060, -1940,
  294, -1001, 374, 1587, 1559, -1502, 14, 2063, -605, 169, 1751, 232, -110,
  -933, 350, 882, -493, 348, 2509, 707, 920, 1298, -2254, 297, 553, 581,
  1956, -232, 406, -548, 543, -2462, -1403, -662, -2183, 1250, -537, -204,
  -304, 1258, -501, -636, -1034, -679, -1524, 760, -710, -2067, 1524, 2716,
  328, 298, 430, -927, 829, 1142, -721, -1444, -2310, 1630, 324, 478, 803,
  -176, -235, 870, 415, -245, 198, -901, 643, 1195, -1174, 797, -407, -881,
  3684, 474, 1531, 641, -937, 1614, -2485, 1650, 1361, 1558, -369, -723,
  1886, 1807, -2354, 463, 473, 23, -442, 1336, -1697, 284, -1688, 923, -358,
  1032, 812, 3219, 888, 797]

theorem fractionalNearFrameSubtreeG2R0551_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0551Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0551Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0551Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0551_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0551LowerBoundTable : List ℤ :=
  [-1692, 2477, 2841, 32, 33, -1234, -648, -1020, 261, 3958, 967, 100, 6443,
  1127, 4871, 687, -1279, 2661, 4478, 4858, 2504, -1852, -1729, 2326, -4157]

def fractionalNearFrameSubtreeG2R0551LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0551Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0551LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
