import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0146`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0146Mask : ℕ := 1370586080318056

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0146Witness : Array ℤ :=
  #[368, -148, 424, -402, -281, 675, 775, 1332, 69, 6, -899, -918, -1175,
  636, -52, -1, 384, -143, -21, 9, -290, 320, -335, -284, 321, 484, -245,
  770, 520, 228, 178, 372, 636, -746, -665, 146, 367, -214, -249, -41, -87,
  -1054, 11, -232, -327, -236, 25, 482, 193, 555, -310, -325, -1061, 891,
  202, 186, -109, 454, 348, 470, -414, -147, -241, -1292, -592, 314, 461,
  -417, 188, -150, -127, -913, 185, -644, 92, -81, 438, 302, -552, -413,
  549, 558, 95, -524, 213, 309, -83, -327, 471, 184, 841, -434, -545, -4,
  -22, 233, -526, 110, -735, 620, -512, 1099, -770, 87, 162, 178, -374,
  -161, -364, -213, 301, -35, 38, 382, 79, 300, -124, 576, 47, 0, -189,
  -1079, 278, 100, -593, 671, -562, 455, 56, -14, -421, 552, 624, 384, 128,
  373, 411, -812, 160, -547, -49, -434, 305, -504, 286, 640, -206, 154,
  -502, 1026, 116, 397, -15, -310, 433, 209, 230, -24, 716, 348, 671, -633,
  -281, -1491, 1006, 155, 273, 215]

theorem fractionalNearFrameSubtreeG2R0146_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0146Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0146Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0146Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0146_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0146LowerBoundTable : List ℤ :=
  [-616, 589, -712, 915, -717, -527, 33, 575, 33, 2047, -1013, 2340, -1770,
  432, 864, 1773, -1314, 1236, 1598, 2334, 2677, -144, 100, 155, -366]

def fractionalNearFrameSubtreeG2R0146LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0146Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0146LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
