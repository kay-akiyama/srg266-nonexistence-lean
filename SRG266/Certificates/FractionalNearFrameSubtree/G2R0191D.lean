import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0191`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0191Mask : ℕ := 1846668068293208

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0191Witness : Array ℤ :=
  #[154, 122, 899, -83, -32, -5, -329, -283, -300, -606, 442, 78, -131, 308,
  26, 523, -221, -188, -535, 380, 270, 237, 210, 215, -35, -125, -707, 100,
  268, -299, 138, 272, 248, 14, -162, -46, -115, 0, 187, -195, 31, -117,
  444, -416, -538, -397, 325, 293, -63, 194, 147, 37, 250, -714, 278, 806,
  692, -271, 130, 1, -300, -529, -114, -559, -696, -189, -55, 115, 298, -74,
  254, 298, -144, 169, 733, -158, 61, -30, 207, 103, 245, 130, 172, 18, 88,
  671, 85, -68, 19, 39, 13, -144, 44, 223, 47, 91, -317, -326, -173, 59,
  -264, 223, -391, 158, -579, 311, -511, -140, -95, 60, -125, -231, 133,
  -122, 33, 66, 100, -181, 34, 554, -43, -27, -68, -386, 359, -337, 5, 84,
  269, 158, 238, 110, -43, 168, 68, -67, 252, -24, 108, 553, -326, 76, -191,
  197, -150, 205, 24, 419, 193, 92, -431, 233, -4, -11, -129, 0, 165, 109,
  568, -264, 323, 193, 52, 564, -288, -780, 37, 399]

theorem fractionalNearFrameSubtreeG2R0191_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0191Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0191Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0191Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0191_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0191LowerBoundTable : List ℤ :=
  [-170, 541, 190, 511, 1, 0, 129, 3, 229, 8, 841, 249, 1, 801, 10, 453,
  122, 413, -133, 1256, 771, 990, 1033, 439, 43]

def fractionalNearFrameSubtreeG2R0191LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0191Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0191LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
