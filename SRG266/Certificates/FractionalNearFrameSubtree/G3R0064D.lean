import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0064`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0064Mask : ℕ := 969076162926090

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0064Witness : Array ℤ :=
  #[-28, 123, 43, -150, 129, 42, 56, -18, -40, 84, 59, -55, -87, -126, -76,
  -134, -114, -206, -18, -39, -67, 112, -49, 86, 109, 2, 67, 50, 47, 70,
  -50, -8, 1, 48, 25, 116, 138, 81, -25, 22, 13, 43, -83, -84, -155, 95,
  -20, 96, 113, 22, 38, 107, -108, 108, 41, 7, 13, 26, 129, -101, -47, 87,
  99, -20, 8, 41, 97, 46, -56, 88, 49, -74, 42, -77, 39, 128, 139, 14, 0,
  -64, 225, 64, 23, -43, -15, 90, 12, 48, -23, -78, 22, -58, -218, -94, 55,
  25, -3, 67, 49, -31, -137, -18, 14, 41, -73, -74, 2, 68, 133, 122, -151,
  -102, -129, -91, -44, -115, -63, -26, -32, -62, 74, 31, 0, -104, -72, -41,
  -41, 138, -104, -106, -82, -62, -67, 119, 66, -11, -83, -46, -16, 31, 39,
  49, -31, -179, -66, 26, 75, 85, -4, -117, -25, 55, 89, -10, 32, 63, 126,
  29, 68, 112, -9, 28, 77, -84, 133, 10, 47, 20]

theorem fractionalNearFrameSubtreeG3R0064_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0064Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0064Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0064Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0064_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0064LowerBoundTable : List ℤ :=
  [-55, 1, 97, 2, 3, 132, 2, -29, 93, 208, -57, -189, 2, 403, 10, 11, 368,
  189, 220, 145, -274, -92, 222, 328, 86]

def fractionalNearFrameSubtreeG3R0064LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0064Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0064LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
