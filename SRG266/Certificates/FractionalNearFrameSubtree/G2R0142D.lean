import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0142`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0142Mask : ℕ := 1362064745922914

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0142Witness : Array ℤ :=
  #[288, -174, 1833, -419, -1058, 693, 0, 2196, 1406, 2949, 2294, -790,
  -1192, -3046, 257, -191, 233, 51, -1389, 129, -2977, -433, 154, -317,
  -898, -33, 1370, 199, 2983, 1290, 1017, 976, 266, 838, 417, -2174, -997,
  875, 901, 0, -227, -1343, -137, 1385, 1529, 1228, -1278, -734, 902, 1065,
  -587, 939, 399, -197, 586, 977, 1634, 418, 81, 525, 1768, 591, 1304, 778,
  -282, 703, -209, -887, 1927, 814, -392, -1132, -1025, 407, -411, -1777,
  -2744, 2034, 39, 747, -692, -1000, -261, 0, 1037, 1048, -670, 1672, 223,
  326, -108, 1520, 3853, 418, 2213, 338, -1479, 510, -172, -114, 910, -990,
  532, 23, -624, -1362, -1526, -548, -1084, 1006, 213, -444, -712, -780,
  102, 1385, -244, -646, 486, -530, -783, -1360, -1425, 1381, 229, 876, 440,
  572, -625, 358, 374, -809, 895, 140, 1784, 285, -1274, -184, 308, -79,
  873, -421, -1033, -411, 308, -2453, -41, -305, -717, -1238, -883, -641,
  -1105, -741, 480, -1327, -197, 345, 578, 64, 1286, -950, 597, -48, 495,
  342, 2340, 397]

theorem fractionalNearFrameSubtreeG2R0142_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0142Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0142Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0142Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0142_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0142LowerBoundTable : List ℤ :=
  [-383, -1618, 32, -1315, 482, 1028, 1410, 1586, 3761, -2234, 101, 647,
  -403, 4976, 1592, 2947, 10482, 2055, -581, 99, 3426, 2129, 8967, 1684,
  4131]

def fractionalNearFrameSubtreeG2R0142LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0142Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0142LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
