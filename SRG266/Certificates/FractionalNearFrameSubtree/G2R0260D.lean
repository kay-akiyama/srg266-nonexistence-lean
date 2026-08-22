import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0260`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0260Mask : ℕ := 5367663988807178

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0260Witness : Array ℤ :=
  #[3, 471, 115, 12, 439, 335, -711, -472, -402, -144, 1244, -217, 136, 332,
  372, -366, -48, 381, 46, 272, -74, -325, -249, 247, -357, 664, -109, -41,
  627, -182, 756, 469, 113, 25, -313, -290, 144, -69, 28, 42, 205, 229,
  -267, 401, 11, 322, 232, -115, -6, 890, -6, -826, -135, 33, 383, -213,
  -347, 671, 548, 55, 621, -341, 374, -319, -721, 406, 0, -567, 92, 296,
  -42, 47, 234, -10, 640, -133, -155, -157, -37, 416, -141, 294, 223, 476,
  -10, 620, -1, 544, -71, -267, 49, -475, -252, 631, 122, 495, 36, 388, 209,
  -132, 159, -616, -184, -461, -538, -50, 532, -540, 105, 420, 423, 139,
  -112, -1008, -489, -113, 433, -239, 475, 8, 37, -373, -105, -147, 490,
  124, 99, 177, -253, 73, -976, -421, 207, 76, -119, -686, -295, 28, -216,
  855, -136, -156, 87, -356, 484, -232, -914, 128, -256, -54, -1075, -1126,
  294, 236, 276, -208, -369, 158, 869, -179, -533, -208, 1250, -315, 333,
  -233, -993, -80]

theorem fractionalNearFrameSubtreeG2R0260_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0260Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0260Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0260Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0260_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0260LowerBoundTable : List ℤ :=
  [-233, -1464, 30, 32, 227, 897, 1641, 31, 33, -403, 721, -825, -67, -815,
  590, -1056, 3476, -545, 99, 212, 99, 2562, -738, 101, 1444]

def fractionalNearFrameSubtreeG2R0260LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0260Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0260LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
