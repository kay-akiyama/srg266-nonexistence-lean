import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0115`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0115Mask : ℕ := 5793795274034185

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0115Witness : Array ℤ :=
  #[127, 168, 96, 18, 237, 95, -146, 11, -67, -83, 47, -64, 84, -218, -271,
  -67, -105, -254, -329, -110, -152, -43, 217, -102, -114, 75, 39, 83, 313,
  73, -144, 288, 129, 208, 216, 99, 70, 64, 14, -69, -49, 117, 229, -73,
  -214, -143, -244, 70, -77, 76, -39, 84, 126, 467, 27, 5, 100, 62, -186,
  109, 132, 7, 0, -37, -143, 0, 51, 129, 38, 135, 83, -34, -98, -33, 61,
  147, -50, 17, -128, -48, -80, -86, 16, 112, 91, 174, 194, 149, -42, 157,
  264, 19, -1, 246, 115, -153, -231, 336, 108, -191, -75, 204, 0, 139, 191,
  -88, 351, 98, -44, -9, -64, -119, -59, 35, 47, -92, -104, -5, 57, -128,
  -195, 149, -192, -141, 3, -262, 123, -29, -42, 174, 330, 19, 62, 13, 98,
  114, -46, -40, -25, 124, 119, 3, 41, 174, -173, 213, 289, -153, 133, 43,
  62, 44, -48, 59, 51, -25, 8, 39, 76, -90, -28, 93, 313, 77, 161, 0, 229,
  86]

theorem fractionalNearFrameSubtreeG5R0115_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0115Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0115Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0115Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0115_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0115LowerBoundTable : List ℤ :=
  [152, 292, 676, 2, 506, 377, 474, 164, 136, 386, 629, 456, -101, 976, 784,
  804, 532, 418, 29, -466, 1147, -189, 694, -207, 9]

def fractionalNearFrameSubtreeG5R0115LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0115Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0115LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
