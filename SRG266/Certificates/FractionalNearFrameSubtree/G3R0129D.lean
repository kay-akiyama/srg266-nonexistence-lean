import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0129`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0129Mask : ℕ := 5403658757380784

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0129Witness : Array ℤ :=
  #[99, -34, -75, 262, 292, 155, -422, -154, -125, 479, 391, 191, 220, 131,
  226, 365, 368, 76, 317, 153, -731, -95, -142, -83, -60, 189, -149, 190,
  -68, 321, 78, 182, -392, 15, 222, -458, -925, -89, 449, 433, -25, 71, 51,
  533, 394, 177, 286, -103, 126, -135, -552, 41, -359, 451, 24, -361, 321,
  262, -101, 210, 243, -101, -174, 112, -2, -327, 547, 62, 563, 89, 47, 162,
  -1, 468, 155, 303, -54, 3, -11, -160, -164, 351, 287, 89, -238, 185, -569,
  -30, -60, -285, 118, 205, 24, 305, -385, 39, 253, 415, 129, 55, -4, -18,
  526, 224, 8, -193, 504, -540, -620, -483, -282, -444, 114, 8, -151, 291,
  1011, 552, 276, 143, 377, 419, 212, -153, 28, -388, 116, 127, 285, 574,
  401, -295, -14, -94, -147, -220, 283, -53, 665, 141, -285, 194, -158,
  -447, -19, 145, 212, 708, -14, -43, -281, -450, -241, -221, -51, -403,
  -85, -909, 24, 279, 616, 522, 0, -4, 78, -213, -752, 0]

theorem fractionalNearFrameSubtreeG3R0129_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0129Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0129Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0129Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0129_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0129LowerBoundTable : List ℤ :=
  [418, 85, 275, 716, -178, 886, 761, 274, 892, 1523, 1061, 668, 1073, -314,
  9, 9, 529, 9, 90, 910, 860, 248, 1116, 1490, -1]

def fractionalNearFrameSubtreeG3R0129LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0129Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0129LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
