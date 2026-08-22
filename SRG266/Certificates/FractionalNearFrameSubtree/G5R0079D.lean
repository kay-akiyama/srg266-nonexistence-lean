import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0079`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0079Mask : ℕ := 5439061067792722

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0079Witness : Array ℤ :=
  #[69, 1463, 335, 377, 332, -432, -1068, 572, -271, 1355, 247, -1466, -145,
  -133, -572, -1415, -841, -1013, 1242, 695, -1091, -1163, -713, -777, 230,
  -355, 799, 2316, 1291, 1563, 280, 204, -525, -35, -127, 0, 123, -72, -945,
  280, -778, 206, 526, -284, -135, 675, -551, 495, 526, 6, -370, 151, -1104,
  -1068, 702, 852, -274, 577, -807, 300, 292, 501, -1887, -222, -1020, 428,
  528, 1305, 827, -544, -454, -438, 239, 252, 355, -674, 87, 387, 1178,
  1088, -140, -959, -17, -405, 1189, -15, -1, -187, 385, 574, 999, 667,
  -916, -444, -87, -815, 797, -362, 2478, -218, 396, 935, 601, -701, -1006,
  -336, 1346, 705, 851, -399, 0, 1109, 248, -367, -186, -193, 179, -693,
  490, -469, -667, 231, -311, 720, 566, 537, 918, 737, -703, -1149, -599,
  -1709, 1221, -40, 456, 1587, -100, 364, 36, 1500, 217, 836, -852, -1225,
  -277, 362, 2614, 54, 1018, 25, -328, 394, -332, 0, -84, -266, 4, -43,
  -801, -1515, -1117, 2268, 155, 124, 136, -776, -788, 280]

theorem fractionalNearFrameSubtreeG5R0079_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0079Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0079Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0079Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0079_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0079LowerBoundTable : List ℤ :=
  [-71, 859, 451, 1713, 583, -685, 767, 637, 247, 46, 3727, 1785, 99, 4157,
  99, -138, 1369, 5548, 1985, 4071, -1581, -1110, -2285, 4251, 620]

def fractionalNearFrameSubtreeG5R0079LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0079Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0079LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
