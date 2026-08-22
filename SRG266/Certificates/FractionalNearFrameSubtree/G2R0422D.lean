import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0422`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0422Mask : ℕ := 5777634753159942

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0422Witness : Array ℤ :=
  #[-83, -278, 354, 407, -443, 27, 624, -69, 734, 0, -361, -210, -233, 429,
  -209, -292, 376, -17, 5, -335, 51, 97, -488, 622, -21, -727, -1099, 310,
  104, 406, 0, -69, -48, 505, 1106, 424, 99, -535, 107, -583, 91, -60, 1521,
  -148, -1113, 178, 212, 686, -1093, 484, 783, 855, 519, -58, -325, -615,
  773, 111, -124, 250, -612, -73, 609, -332, 917, -31, -35, -76, 323, 91,
  344, 0, -626, 662, 745, 250, 1045, -399, -533, 257, 920, 409, 158, -431,
  290, -10, 434, -577, -167, 138, -810, 318, 206, 641, 289, 710, 986, 22,
  98, 226, 593, -150, 485, 757, -363, 679, 255, 542, -1022, -432, -580, 339,
  13, 677, -230, 400, -303, -896, -172, -481, -275, -302, -477, 660, -294,
  -86, 161, -633, -456, -728, 102, 299, 195, -323, -750, -668, 649, -736,
  -361, -252, 94, -69, 58, -134, -55, 466, -252, 672, 498, 447, -414, 588,
  77, 492, -222, 195, 507, 624, -655, 253, 826, 156, 0, 209, 367, 584, 743,
  252]

theorem fractionalNearFrameSubtreeG2R0422_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0422Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0422Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0422Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0422_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0422LowerBoundTable : List ℤ :=
  [240, 384, 1342, 112, 391, 407, 312, 689, 1929, 2000, -1249, 101, 1774,
  4277, 1566, 1350, 3144, -747, 2208, 2128, 3212, 100, 1243, 1473, -1043]

def fractionalNearFrameSubtreeG2R0422LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0422Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0422LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
