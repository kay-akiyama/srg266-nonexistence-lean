import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0150`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0150Mask : ℕ := 1039750667750056

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0150Witness : Array ℤ :=
  #[25, 33, 94, -53, -56, -88, 48, -23, -27, -27, -131, 53, 45, -3, -45, 54,
  10, -13, -48, -55, 13, 53, -19, -21, 31, 76, -6, -21, 19, -43, -31, 1, 79,
  50, 44, 56, 50, -52, -165, 91, 90, 5, 59, 92, 17, 57, 63, 29, 92, 74, -5,
  -79, -62, 2, -36, -92, 34, 45, 8, -53, -22, 21, 46, -71, 68, 26, -70, -48,
  -58, 49, -23, 22, 161, 14, -61, 18, -21, 212, 35, -33, -72, 11, -16, -35,
  -5, 10, 6, 68, 115, 79, -25, 47, 121, 41, 33, 27, 5, 114, 157, 98, 59,
  169, -56, 50, 2, -51, -77, -57, 54, -4, -100, 176, 110, 52, 82, -6, -47,
  74, 63, 18, 147, -16, 0, -62, -14, -34, 106, -35, 29, 41, -6, -63, -51,
  94, -10, -25, 37, 34, 7, -17, -37, -25, 4, 20, -16, -1, -94, -54, -77,
  -113, 25, -44, 234, 100, 70, 22, 105, 160, 93, 43, -53, -2, 104, 84, -7,
  -8, 12, 106]

theorem fractionalNearFrameSubtreeG1R0150_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0150Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0150Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0150Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0150_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0150LowerBoundTable : List ℤ :=
  [157, 244, 270, 38, 213, 165, 217, -113, 176, 295, 202, -96, 326, 563,
  153, 195, 196, 793, 65, 41, 271, 284, 42, 532, 369]

def fractionalNearFrameSubtreeG1R0150LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0150Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0150LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
