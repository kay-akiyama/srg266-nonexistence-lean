import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0166`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0166Mask : ℕ := 6856952473886232

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0166Witness : Array ℤ :=
  #[-47, -3, -73, 71, 59, 128, 4, -80, 199, -39, 35, 56, 21, 47, 28, 23, 52,
  -3, 10, 150, 81, 24, -13, -51, -31, -88, 37, 71, -92, -105, -31, -77, 27,
  192, 82, 75, 9, 153, 0, -40, 20, -44, -74, 79, -125, 53, 84, -2, -65, -57,
  37, 162, -45, 111, -115, -86, 93, -5, 41, 109, 231, 167, 126, 104, 177,
  93, 25, 60, 160, 78, -128, -26, 125, 0, 206, 0, -98, -114, 89, 29, 211,
  -4, 54, -63, 10, -149, 34, -55, 15, 173, 44, -20, -61, 37, -75, -69, -127,
  -87, -110, 16, 19, 168, 121, 271, -237, 105, -202, -158, 95, -98, -58,
  -49, -43, 72, 158, -20, 17, -52, 266, 85, -61, 163, 88, -87, 239, 131, 6,
  68, 94, -102, 156, 42, 53, -8, 2, -49, -22, 11, -49, -60, 12, 58, -56, 94,
  21, -251, 98, 35, 85, 48, -80, 47, 121, 103, 5, 102, -121, 97, 283, -82,
  110, 77, 0, 222, 0, 30, 52, 87]

theorem fractionalNearFrameSubtreeG3R0166_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0166Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0166Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0166Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0166_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0166LowerBoundTable : List ℤ :=
  [196, 419, 482, 314, 331, 244, 94, 22, 387, 658, -116, 355, 836, 683, 417,
  481, 159, 213, 538, 122, 827, 219, -50, 134, 414]

def fractionalNearFrameSubtreeG3R0166LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0166Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0166LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
