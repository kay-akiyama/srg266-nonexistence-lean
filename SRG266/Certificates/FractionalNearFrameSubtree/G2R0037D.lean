import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0037`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0037Mask : ℕ := 883719201072131

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0037Witness : Array ℤ :=
  #[0, -216, 13, -60, -194, -172, -24, -6, -129, 57, -30, 107, 0, 107, 84,
  70, 157, 139, -71, 25, 89, -1, -38, -39, 187, 259, 188, 304, 217, -175,
  -169, -181, -299, -87, 103, 28, 178, 6, -72, -25, -33, 37, -52, -31, 4,
  84, 80, 79, 97, -72, 0, 159, 134, -277, -248, 226, 210, 100, -252, -180,
  88, 66, 51, -38, 107, 46, 40, 29, -60, -60, 157, -129, 38, -19, -179, 126,
  -39, -34, 16, 68, -28, 26, 99, 67, -32, 104, -36, 44, 49, 104, 93, 3,
  -145, -47, -98, 133, 170, 2, 14, 126, -6, 94, -33, 217, 81, 137, 24, 40,
  -8, -141, -25, -80, -66, -39, -181, -70, -75, 149, 21, 47, -44, -36, -30,
  31, 79, 80, 47, -13, -30, 96, 34, 39, -31, 39, 90, 27, 56, 60, -26, 6,
  169, -32, -75, 66, 71, -21, 99, -30, 7, -33, 110, 4, -85, 142, -62, -18,
  0, 20, -27, 89, -29, -3, 70, 72, 13, 94, 54, 0]

theorem fractionalNearFrameSubtreeG2R0037_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0037Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0037Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0037Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0037_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0037LowerBoundTable : List ℤ :=
  [102, 370, 355, 274, 50, 120, 315, 1, 57, -160, 132, 322, 54, 391, 386,
  464, 529, -64, 8, 272, 173, 486, -274, 9, 173]

def fractionalNearFrameSubtreeG2R0037LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0037Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0037LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
