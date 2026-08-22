import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0099`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0099Mask : ℕ := 2520331525784162

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0099Witness : Array ℤ :=
  #[26, -85, -112, -28, -18, 19, 63, 71, -30, 7, 14, 1, 103, -97, -157, -17,
  101, 3, -33, 18, 5, -45, -35, 5, -62, -80, 30, 42, 26, -51, -130, 24, -62,
  -80, -247, 129, 127, 72, 125, 20, 34, 82, -115, -48, -121, -33, 7, -91, 2,
  4, -37, 58, 28, -77, -27, 53, 67, 50, 19, 30, 33, -9, 104, -59, 82, -65,
  0, -42, -66, -59, -140, 87, 185, 134, 53, 61, 42, -28, 11, -6, 12, -7,
  -48, -43, 30, 83, -69, 32, 20, 1, -36, -21, -104, 40, -20, 34, 64, 146,
  -2, 145, 194, 92, 93, -128, -180, 79, -94, -83, -114, -6, 12, 21, 45, -36,
  -8, 5, -57, -62, 8, -3, 33, -131, 18, 0, 80, -22, -98, 43, -89, -18, -110,
  -109, -10, 20, 42, 61, 65, -2, 0, 51, -18, 28, 50, 27, 0, 3, -11, 14, -10,
  -54, 106, 22, 64, -90, 2, 1, -16, -173, -119, -84, -36, 48, 225, -67, -41,
  -93, 150, 37]

theorem fractionalNearFrameSubtreeG3R0099_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0099Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0099Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0099Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0099_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0099LowerBoundTable : List ℤ :=
  [-119, -52, -140, -72, -25, 72, 58, 3, 2, 10, -22, -11, -100, 300, 11,
  -455, 141, 158, 150, 9, -418, 17, -51, 234, 140]

def fractionalNearFrameSubtreeG3R0099LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0099Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0099LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
