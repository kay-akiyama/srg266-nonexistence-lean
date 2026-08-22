import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0101`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0101Mask : ℕ := 2521277490696804

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0101Witness : Array ℤ :=
  #[59, -318, 210, -835, -721, 623, -408, 205, 572, -414, 500, 244, 293,
  -27, 52, 191, -626, -183, -351, 11, -594, 159, 70, 52, -88, 213, 236, 239,
  -659, 542, 23, -415, -106, -73, 438, -39, -418, 591, 228, 169, 70, -72,
  469, -963, 474, 238, -379, -145, 623, -6, -88, -335, -681, 387, -195,
  -365, 96, 179, -208, -125, -600, -231, -4, -203, -1054, 702, -201, 1152,
  59, -607, 56, -63, -278, -295, -1022, -443, -714, 134, 178, -528, 594,
  -495, -1039, -832, 616, 918, 1305, 168, 138, 61, -143, 333, -278, 325,
  338, 152, -388, -369, -543, 420, -22, -467, 38, -752, 387, -19, 334, 105,
  411, 130, 975, -226, -206, -273, -574, -231, 110, 203, 436, 508, 398,
  1944, -1295, -677, -414, -102, 351, 266, -310, -584, 0, 42, 142, 412, -14,
  -345, 124, 364, -19, -8, -377, -326, 1341, -561, 655, 269, 1121, 619,
  -122, -1356, -685, 833, 974, 553, -194, -128, 264, -113, 174, 156, 0, 191,
  814, 1178, -457, 495, 1016, 285]

theorem fractionalNearFrameSubtreeG3R0101_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0101Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0101Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0101Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0101_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0101LowerBoundTable : List ℤ :=
  [-510, 2032, 32, -224, -85, 33, 626, 176, -546, 1741, 2494, 2610, -1730,
  1709, 1914, -1737, 836, 100, -2147, 996, 100, 1813, -152, -2073, 2576]

def fractionalNearFrameSubtreeG3R0101LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0101Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0101LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
