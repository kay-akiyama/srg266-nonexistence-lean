import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0642`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0642Mask : ℕ := 20340649216644614

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0642Witness : Array ℤ :=
  #[-66, -112, -315, -633, -1205, -996, -1320, -860, 595, -1884, -1140,
  1123, 991, 1575, 275, 757, -319, 70, 1257, -830, -741, 117, -99, -466,
  -428, -640, -185, -253, 693, 261, -595, 0, 112, 500, -425, 497, -787,
  -590, 328, 1126, 383, 24, 0, -245, 218, 375, 29, 108, 349, -187, -38, 993,
  -488, -134, -326, 154, 522, 323, -1889, -1851, -600, 986, 424, -221, 354,
  1250, -602, 16, 31, 296, -1356, -515, -435, -896, -335, 995, -388, -137,
  1048, -1190, 418, -100, 401, -774, -270, -302, 955, 1, -23, 259, -321,
  915, -183, 736, 227, 392, 622, 423, 655, 39, 28, 353, 541, -296, 250, 310,
  713, -541, -33, 326, -100, 202, -91, 970, 221, 188, 287, 11, -319, 102,
  300, 666, -21, -320, -402, 515, 315, -289, -923, -468, 31, -261, 1393,
  636, -428, -169, -1484, -278, 1075, -50, 830, 848, -513, 268, 837, 637,
  311, 494, 793, -527, 338, 322, 270, 291, 359, 134, -342, 37, -954, -219,
  146, 146, -2349, -565, 222, -2087, 317, 184]

theorem fractionalNearFrameSubtreeG2R0642_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0642Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0642Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0642Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0642_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0642LowerBoundTable : List ℤ :=
  [-1345, 31, 32, -584, 31, -867, 31, 761, 33, 568, 1665, 817, 1468, 588,
  3161, 909, 1404, -172, -1877, 99, -1329, 100, 699, -930, 100]

def fractionalNearFrameSubtreeG2R0642LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0642Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0642LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
