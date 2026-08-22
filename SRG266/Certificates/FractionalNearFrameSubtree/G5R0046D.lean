import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0046`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0046Mask : ℕ := 4772117513625861

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0046Witness : Array ℤ :=
  #[-703, -494, 5, 673, -360, -108, 397, 365, 858, 567, 299, -261, -801,
  -1062, 87, -327, -639, 6, -428, -40, -312, -127, 6, 62, -111, 264, -591,
  644, -633, 704, 901, 0, -589, -41, 874, 147, 219, 19, -89, 395, -230,
  -392, 25, -485, 772, -302, 151, -383, -26, 562, -21, -531, 616, 574, 254,
  63, -789, -601, 192, 594, -258, 956, -917, 875, 388, -273, 0, 52, -305,
  -218, -604, 1094, 671, 156, 266, -452, 141, -402, -1053, 785, 389, -1254,
  272, 228, -337, 948, -664, 174, -330, 203, 890, 971, -699, 780, 71, 8,
  -23, 392, -468, -527, -90, 1153, -136, -312, 145, 1387, -307, 609, -283,
  103, -523, -85, -689, -192, 728, -1168, 469, -826, -304, 73, 567, 1210,
  1095, 249, -675, -124, 391, -67, -269, 328, -1099, 415, 0, 15, 340, -246,
  454, 539, 360, -452, -554, 508, 434, -130, -321, 475, 222, 277, -530, 525,
  631, -231, 423, -717, 177, -39, 980, -1037, -659, 205, -470, 226, 211,
  992, -344, -274, 546, 765]

theorem fractionalNearFrameSubtreeG5R0046_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0046Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0046Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0046Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0046_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0046LowerBoundTable : List ℤ :=
  [-436, 495, -269, 480, 631, 187, 32, 33, 32, 1082, 2014, 2686, 2544, 431,
  2937, 351, 1713, -585, 980, 2271, 282, -904, 99, 2494, 1071]

def fractionalNearFrameSubtreeG5R0046LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0046Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0046LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
