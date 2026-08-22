import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0150`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0150Mask : ℕ := 1376329427484882

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0150Witness : Array ℤ :=
  #[84, 74, 111, -160, -96, -237, 166, 131, 106, -138, 58, -15, -63, -70,
  -51, 36, -83, 175, 150, 132, 110, 151, 98, -18, 48, -97, -44, -169, -135,
  -220, 68, 18, -351, -224, -274, 53, 123, 211, 122, 186, 17, 35, 18, 137,
  21, -70, 82, -171, 243, 181, -357, -89, 125, 99, 217, -191, -158, 74, 71,
  89, -281, -16, 111, 3, -109, -70, 8, -76, -211, -112, 161, -77, 42, 8,
  -55, -30, 34, 90, 56, 168, -11, 58, 1, 134, -4, -184, 16, 35, 3, -11,
  -213, 122, 257, -67, 200, 145, 66, 125, -21, 75, 0, 117, 143, 213, 95,
  -134, 49, 58, 158, -126, -136, -256, -67, 65, -44, -158, -80, 68, 88, -6,
  -27, -73, -80, 121, -180, -21, -86, 30, 30, 180, 171, 160, -257, 21, 317,
  110, -213, -56, -110, 42, 161, -10, 68, -64, 235, 215, 150, -196, 3, -265,
  -212, 186, -286, 90, -31, -102, -31, 133, 2, 17, 229, 183, -25, -98, 100,
  -159, 113, 205]

theorem fractionalNearFrameSubtreeG2R0150_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0150Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0150Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0150Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0150_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0150LowerBoundTable : List ℤ :=
  [-122, 2, 154, 115, 245, -79, 3, 166, -21, -335, 681, 189, 9, 700, 476,
  376, -262, 485, 119, -16, -157, 143, 403, 345, 10]

def fractionalNearFrameSubtreeG2R0150LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0150Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0150LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
