import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0152`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0152Mask : ℕ := 6850224353097228

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0152Witness : Array ℤ :=
  #[-1004, -1826, -1918, -1182, -493, 231, 683, 752, 500, 574, 591, 890,
  598, 313, 416, 1031, 281, 160, 285, -629, 1201, -49, 652, -1027, 683, 126,
  -452, -98, -566, -891, 192, 204, 186, -412, 916, 740, -478, -473, -678,
  -1146, 306, 816, -56, -342, 191, 732, 485, -689, -142, -673, 435, 1088,
  424, 682, -421, -39, 250, 608, -242, 892, 232, -616, 1127, 303, 358, 476,
  175, 27, -1132, 591, 1119, 0, 371, -168, -82, -644, 363, -8, 934, -1079,
  -549, -1332, 531, 723, 458, 250, 975, 808, -1141, -542, -354, 554, 237,
  -343, 470, 824, 469, -1275, 927, -594, 310, -1256, -160, 296, -914, -332,
  642, -685, 197, 425, -399, -196, -48, 39, 247, 1030, -16, -23, 154, -1037,
  -904, -347, -543, 246, -488, 271, 8, -4, 1360, -229, 44, -296, -131, -809,
  -232, -634, -550, -131, -151, -356, -487, -724, 209, -409, 592, -1058,
  195, -605, -508, 148, 490, -507, 767, 1038, 1174, -1141, 96, 173, 257,
  -1057, 566, 637, 197, 1183, 52, 536, -477, -981]

theorem fractionalNearFrameSubtreeG3R0152_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0152Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0152Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0152Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0152_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0152LowerBoundTable : List ℤ :=
  [-619, 32, 1863, -18, -154, 31, -448, 43, 100, -4313, -334, 2263, -535,
  1310, 613, 2821, 2320, -717, 1909, -2863, 100, -361, 26, 99, 1874]

def fractionalNearFrameSubtreeG3R0152LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0152Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0152LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
