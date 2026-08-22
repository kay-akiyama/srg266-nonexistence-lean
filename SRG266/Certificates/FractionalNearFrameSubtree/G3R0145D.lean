import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0145`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0145Mask : ℕ := 6848300209903114

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0145Witness : Array ℤ :=
  #[75, -39, 82, 29, -35, 21, 9, -9, -51, -74, 19, -29, -19, -50, -18, -32,
  40, -82, 32, -58, 11, -37, -7, 34, -61, 15, 18, -58, 10, -26, 11, 48, -64,
  19, 42, 2, -26, 1, -5, 81, 33, -32, -79, -92, 65, 48, 86, 49, -22, 83, 47,
  -60, 135, 56, 20, -19, 15, 6, 10, 29, 72, -36, -14, -58, 35, -21, 11, -28,
  62, -54, 33, 29, -1, 5, -101, -45, 45, -41, 40, 29, -16, 13, -52, -18, 68,
  -30, 18, 72, 49, 86, 30, -32, 47, 17, 75, 44, 33, 63, 42, -2, -31, 44,
  -16, -12, -47, -93, -8, 20, 117, 81, -11, 42, -9, -53, -92, 23, -30, 42,
  50, 58, 6, -55, -61, -28, -3, -39, 47, -26, 70, -52, 16, -13, -28, 22, 26,
  14, 84, 14, -8, -41, 69, 67, -12, 75, -37, 23, -43, 39, 29, -31, 78, 17,
  86, 1, 16, 22, 89, 155, -34, -33, 58, -25, 68, -38, 0, -62, 23, 20]

theorem fractionalNearFrameSubtreeG3R0145_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0145Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0145Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0145Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0145_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0145LowerBoundTable : List ℤ :=
  [60, 142, 133, 111, -9, 106, 83, -88, 69, 147, 123, 116, 192, 10, 432,
  -60, 9, 183, 152, 242, 26, 143, 359, 187, 44]

def fractionalNearFrameSubtreeG3R0145LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0145Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0145LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
