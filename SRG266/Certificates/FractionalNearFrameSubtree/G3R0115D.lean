import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0115`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0115Mask : ℕ := 5388415866081954

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0115Witness : Array ℤ :=
  #[-150, -792, -114, 499, 35, 364, 0, -1356, -143, 211, -194, 410, -301,
  150, 1459, 496, -134, -667, 91, 28, 622, -45, -759, 365, 534, 264, 23, 31,
  74, 402, -48, -104, -25, -142, -652, 252, 235, 270, 135, -59, 211, -344,
  98, 119, -132, 663, -801, -821, 549, 420, 794, -9, 326, 643, -92, 23,
  -223, -444, -234, -311, 516, 68, 212, 259, -234, 15, -206, -578, 38, -373,
  561, 442, -593, -310, -82, 749, -796, 3, 260, 158, -496, -75, -369, -673,
  -161, -728, -662, 264, 599, 936, 615, 716, 136, -574, -701, 392, -110,
  -266, 314, -203, -48, -112, -67, 901, 471, 54, 312, 241, -230, 357, -651,
  -300, 206, 112, -19, -121, -83, -526, -528, 827, 1464, 112, 136, -392,
  295, 549, -288, -1176, 444, 439, -206, -928, -582, -330, 681, 355, 183,
  93, -289, 412, 0, -875, 205, 26, -75, 338, -96, -594, -524, -24, 164, 287,
  -92, 168, -113, 590, -395, 107, 507, -370, 818, 380, 0, -295, 6, 582, 274,
  -1148]

theorem fractionalNearFrameSubtreeG3R0115_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0115Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0115Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0115Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0115_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0115LowerBoundTable : List ℤ :=
  [-380, 127, 31, 593, 32, 186, 32, 1170, -564, 100, 100, 576, 1264, 2275,
  440, 1675, 1225, 289, -111, 100, 99, -90, -424, -1597, 101]

def fractionalNearFrameSubtreeG3R0115LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0115Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0115LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
