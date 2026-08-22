import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0046`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0046Mask : ℕ := 960546255635018

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0046Witness : Array ℤ :=
  #[105, 38, 10, -19, 46, 14, -64, -8, -150, -102, -144, 82, 44, 31, -88,
  196, 69, -9, 16, 64, 0, -37, -2, 86, -49, -38, 9, 84, 5, -123, -46, -41,
  -10, -58, -95, 196, 143, 76, -40, 193, 0, 191, -100, -79, -26, -59, -77,
  -11, 80, 61, 68, 81, 108, -22, 59, -63, 136, 2, -32, 27, 5, 32, 13, 56, 4,
  -101, 31, -3, -38, 10, 8, -11, 30, 2, -4, -64, 54, -62, -38, -20, -53,
  -38, 1, -2, 62, 2, 70, -43, 16, -6, 26, -5, 79, -64, 28, 55, -79, -2, 9,
  -18, 1, 13, 55, 16, 53, -74, 54, -4, 1, 34, -58, 66, 0, -49, -56, 98, 32,
  -40, -15, -53, -8, -117, -98, 90, 31, 15, 62, 14, 41, -12, -55, 11, 35,
  -115, -93, 1, 17, 4, 66, 66, -2, -71, 57, -27, 26, 115, -72, -22, 26,
  -109, -2, 81, -8, 53, -124, 25, 93, 39, -56, -13, 91, 118, 104, -221, 22,
  67, -7, 43]

theorem fractionalNearFrameSubtreeG3R0046_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0046Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0046Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0046Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0046_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0046LowerBoundTable : List ℤ :=
  [11, 22, 92, -151, 88, 180, 1, 86, 135, 53, 54, 135, 12, 244, 10, 230,
  -84, 73, 51, -121, 19, 250, 37, 345, 282]

def fractionalNearFrameSubtreeG3R0046LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0046Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0046LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
