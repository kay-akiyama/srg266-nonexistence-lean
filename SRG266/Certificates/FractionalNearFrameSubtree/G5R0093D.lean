import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0093`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0093Mask : ℕ := 5510254443532884

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0093Witness : Array ℤ :=
  #[40, -26, 74, 88, -180, -16, 68, -61, -50, -10, -50, 11, 0, 78, -89, 53,
  152, -1, -98, 54, -3, 44, 80, -49, 54, 37, -87, -81, -69, -46, 27, 131,
  234, 152, -121, 130, -87, -100, 0, -59, -53, -123, -129, -160, -142, -155,
  128, -16, -208, -367, -87, 216, 198, -104, -58, -208, 255, 110, 276, 32,
  -147, 105, -132, 229, 83, 55, 20, 5, -80, 54, 69, -56, -203, 119, 85, 76,
  -82, 35, 64, -14, 177, -70, 76, -140, -199, -204, 39, 94, -48, 53, 58,
  -126, 84, 4, -34, -64, 77, -48, -109, 168, 21, 124, 122, -36, 116, -35,
  266, -83, -68, 123, 35, -20, -23, -36, -64, 26, -80, 69, 45, 167, 81, 39,
  -18, -16, -236, -175, 73, 99, -21, -96, -146, 24, -32, -83, 114, 0, -18,
  97, 12, -14, 56, 50, -20, -7, 64, -192, 14, 125, 53, -43, -92, 48, -12,
  -14, 144, 166, 138, 4, -32, 75, 47, 11, 0, 119, 117, -14, -19, 48]

theorem fractionalNearFrameSubtreeG5R0093_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0093Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0093Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0093Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0093_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0093LowerBoundTable : List ℤ :=
  [-148, 26, 184, 15, 2, 2, -21, 88, -65, 742, 53, 23, 2, 99, 208, 51, 215,
  -462, 457, 306, -218, 42, 518, 731, -139]

def fractionalNearFrameSubtreeG5R0093LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0093Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0093LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
