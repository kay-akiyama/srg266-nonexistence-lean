import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0135`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0135Mask : ℕ := 1354096254239308

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0135Witness : Array ℤ :=
  #[345, 1573, 447, 34, 112, 528, 418, -307, -94, -2155, 983, -767, -1461,
  563, -316, -1030, 128, 1239, -110, 211, 172, 441, -179, 46, 125, -31, 411,
  54, -111, 352, 320, -595, -419, -1153, -156, 1226, 603, -432, -614, -627,
  1587, 1720, 1224, 686, 852, 896, 1242, -480, 1328, -1268, -39, -155, 87,
  -165, -26, -1109, 280, -78, -136, 46, -187, -200, -89, -227, 50, 518,
  -477, -419, 340, -278, 131, -896, 496, -929, 410, 265, 241, 361, 111, 195,
  319, -662, 321, -1401, -663, -285, 637, -617, 1257, 107, -26, 512, -53,
  912, -187, 530, 54, 207, 927, 248, 1055, 136, -241, 148, -196, 1453, -604,
  234, -37, -295, -494, 882, 847, 44, 58, -946, -151, -773, 641, 1057, 2530,
  51, -12, -270, 121, 1048, -20, 47, 612, -747, 790, -860, -136, -591,
  -1366, 0, 308, 431, -557, -476, -717, 888, 825, 275, 94, 1884, -399, 475,
  -45, -21, -44, -383, 703, 599, 2436, 828, -11, -259, 903, -1041, 1491,
  191, 65, -369, -609, -812, 801, -378]

theorem fractionalNearFrameSubtreeG2R0135_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0135Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0135Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0135Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0135_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0135LowerBoundTable : List ℤ :=
  [603, 1556, 1077, -722, 2815, 3369, 986, 1837, 30, 4580, 2011, 2134, 1512,
  1256, -326, 1273, 2698, 100, 2338, -636, 1415, 5250, 349, 575, 101]

def fractionalNearFrameSubtreeG2R0135LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0135Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0135LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
