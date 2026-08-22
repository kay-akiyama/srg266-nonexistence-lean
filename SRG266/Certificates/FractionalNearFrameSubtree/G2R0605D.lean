import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0605`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0605Mask : ℕ := 7041165343429778

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0605Witness : Array ℤ :=
  #[54, 121, 103, 60, 116, 26, -146, -28, 86, -49, -76, -123, -174, -260,
  40, -157, -104, -48, 27, -70, -77, -38, 124, -81, 12, -94, 7, -18, 125,
  -10, -154, -144, -181, 53, 264, 146, -58, 81, 68, 183, -76, -104, -126,
  -79, -31, 38, 39, -218, 51, 118, 40, 36, -58, -247, -75, -103, 91, 32,
  223, -59, 7, 3, -38, -26, 59, -180, 139, 6, -46, -24, 159, -37, -1, -10,
  -69, 50, 72, -142, -8, -4, -38, 0, 154, -241, 62, 36, 30, 12, -59, 74,
  -56, -203, 116, 140, -168, 67, 13, -86, 64, -32, 38, 37, 84, -129, -62,
  -16, -165, 28, -5, 37, 158, 81, -21, -157, -75, 156, 181, 139, 270, -130,
  -226, 0, 26, -166, -189, 56, -117, -94, 88, -172, 134, 14, -231, 77, 155,
  -60, 127, 85, 54, -166, -70, 0, -153, -2, -65, 55, -25, 91, 68, -135, 118,
  -28, -99, 182, 29, -38, -25, 58, 43, 85, -10, 124, 150, -146, 23, 72, -29,
  120]

theorem fractionalNearFrameSubtreeG2R0605_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0605Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0605Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0605Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0605_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0605LowerBoundTable : List ℤ :=
  [-279, 61, -36, 156, 2, -332, 66, 1, -94, -86, 11, -139, -301, 388, 9,
  -283, -147, -199, -211, 413, 10, 9, -53, -422, -31]

def fractionalNearFrameSubtreeG2R0605LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0605Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0605LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
