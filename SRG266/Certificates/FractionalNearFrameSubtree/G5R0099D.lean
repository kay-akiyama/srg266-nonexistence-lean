import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0099`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0099Mask : ℕ := 5541767633551762

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0099Witness : Array ℤ :=
  #[-188, -63, 219, -142, 29, 30, 105, 30, 182, 75, 223, -164, -63, -201,
  -113, -33, -1, -9, 33, 175, 138, -115, 79, 56, 51, 41, 1, 1, -214, -23, 0,
  -29, -76, 29, 99, 200, 18, 122, 128, 115, 3, -46, -154, 24, 117, -10, -90,
  48, -74, 173, 130, 95, 26, -147, 65, 66, 214, -16, -58, -153, -90, -159,
  27, -25, 28, 95, 74, -152, 0, 271, 2, -26, -37, -107, -12, 7, -273, 55,
  136, 136, -77, 163, 91, -62, 55, -44, -32, -112, 203, -158, 75, -140, -79,
  209, 274, 73, -38, -143, 7, 7, 88, 80, 105, -93, 23, 96, -22, -16, 164,
  -7, -40, 36, -24, 55, 96, 20, 45, -53, -119, 154, -141, 7, 75, 19, 97,
  181, 124, -3, 74, 87, 50, 48, 53, 146, -54, -66, -94, -20, -15, -237, 175,
  111, -10, 192, 96, 57, 18, 86, 47, 114, 60, -18, 39, -74, 27, -71, -58,
  58, 48, 127, 103, 52, 183, 282, -39, -100, 151, -100]

theorem fractionalNearFrameSubtreeG5R0099_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0099Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0099Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0099Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0099_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0099LowerBoundTable : List ℤ :=
  [139, 374, 240, 263, 515, 69, 182, 178, 150, 521, 970, 98, 10, 353, 388,
  214, 47, 628, 9, 407, 11, 566, 217, 613, -198]

def fractionalNearFrameSubtreeG5R0099LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0099Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0099LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
