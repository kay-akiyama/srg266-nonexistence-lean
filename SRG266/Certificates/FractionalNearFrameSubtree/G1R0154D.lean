import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0154`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0154Mask : ℕ := 1039884153688304

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0154Witness : Array ℤ :=
  #[7, 36, 0, 5, -56, 46, 94, 6, 74, -64, -38, -68, -44, -27, 24, -41, 26,
  43, -56, -43, -21, 7, -11, -175, 57, 50, 52, 49, -25, -113, 19, 51, -43,
  140, -71, -15, 12, 125, 93, 84, 0, 75, -76, -45, 0, -56, 107, -37, 36,
  130, 80, -4, 111, 75, 195, -18, -140, -30, 68, 27, 53, -7, 42, -25, 69,
  41, -88, 63, 47, 37, 73, 2, 92, 71, -82, 75, -25, -91, -161, -12, 42, 105,
  153, 180, 4, 48, 56, 68, 162, 46, 3, -23, 159, -48, 80, 98, -125, -26, 66,
  -54, -64, 95, 0, 45, -34, -114, 71, -30, 66, 39, 37, -145, -12, -59, -102,
  -18, 90, -30, 13, -160, 42, 58, 96, -182, -75, -66, -27, 5, -56, 127, 28,
  -223, -28, 20, -23, -52, 91, -90, -5, -3, -163, -206, 10, 97, 102, 23, 17,
  49, 37, -3, 34, -98, 27, 172, 21, -46, -64, 95, 7, 11, -53, -68, -31,
  -179, -117, 50, -49, 120]

theorem fractionalNearFrameSubtreeG1R0154_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0154Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0154Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0154Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0154_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0154LowerBoundTable : List ℤ :=
  [-5, -137, 81, 23, 121, 45, 109, 33, 196, -205, 312, -139, -74, -50, 454,
  -97, 447, 254, 147, 199, 245, -226, 117, 357, 10]

def fractionalNearFrameSubtreeG1R0154LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0154Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0154LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
