import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0202`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0202Mask : ℕ := 6880035775127064

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0202Witness : Array ℤ :=
  #[-231, 374, 9, -554, -161, -600, -656, 282, -819, -21, 6, 858, 376, 502,
  584, 1036, -186, 536, 280, 439, 318, 352, 620, -94, -438, -412, -964,
  -522, -729, -854, 1076, -1084, -1, 1196, 1292, 508, -23, 647, 363, 612,
  1005, 366, 326, 459, -303, 1101, -903, -1163, -918, -39, -100, 771, -624,
  849, 784, -1757, 376, 141, 409, -334, -365, 784, -72, -495, 1638, 159,
  -334, 238, -312, -1563, 446, 696, -574, 871, -532, -212, 1297, 518, 155,
  794, 754, 984, 319, 613, 768, -1259, 310, -403, -244, -235, -496, 889,
  300, 259, 76, 441, 180, -799, 84, -432, 273, 317, 684, -547, 714, -836,
  -554, -91, -762, -521, -177, -229, 640, -893, -930, -149, 764, 2638, 1106,
  645, -1116, -349, -921, 185, -192, -690, -921, 96, 169, 305, -157, -321,
  -837, -522, 595, -268, -910, 1177, 528, -1016, -41, 902, 0, 917, 747,
  -536, 589, 304, 328, 177, 1377, -962, -145, -511, -597, 1111, 15, 636,
  211, -494, 412, 686, 267, -388, 241, 425, 515, 302]

theorem fractionalNearFrameSubtreeG3R0202_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0202Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0202Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0202Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0202_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0202LowerBoundTable : List ℤ :=
  [-48, 33, 2639, 2163, 1741, -1031, 1760, -1275, 730, 335, 7067, -2603,
  1234, 4416, 3138, 1616, 100, 282, -1276, 1946, 3223, 1852, 2801, 100,
  -2736]

def fractionalNearFrameSubtreeG3R0202LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0202Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0202LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
