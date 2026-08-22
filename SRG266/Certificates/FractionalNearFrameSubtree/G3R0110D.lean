import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0110`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0110Mask : ℕ := 5385120615337482

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0110Witness : Array ℤ :=
  #[-42, -28, 121, -119, -3, 40, 17, -182, 0, -54, -116, 148, 134, 97, 213,
  154, -130, -60, 48, -116, -17, 185, -50, 105, 197, 10, 54, 30, -179, 229,
  -69, 74, -95, -22, -20, 97, 21, 16, 131, 44, 101, 56, 20, 99, -123, 71,
  -7, -34, -84, -80, 87, 69, 50, 137, -107, -36, 81, 28, -72, 153, 41, 4,
  192, 0, -165, 64, 10, 53, 53, -155, 30, 62, -139, -143, -168, -29, 179,
  25, 94, 130, 29, 122, 10, -157, 109, 23, -82, 19, 144, -46, 17, 92, 157,
  -56, 154, 50, -11, -23, 34, -6, -8, 32, -57, 67, 81, 134, 71, -70, 72, -5,
  -63, -223, -61, -3, 149, 45, -123, 114, 31, 87, 95, 0, -137, 84, -29, 7,
  114, 273, 96, 104, 8, -40, -34, -1, 20, -27, 30, -106, 106, -21, -143,
  -74, 32, -49, 43, 88, -93, 162, 6, 63, 143, 53, 19, 88, -195, -104, 55,
  149, 15, 123, -69, -74, -168, 170, -1, 68, -42, -393]

theorem fractionalNearFrameSubtreeG3R0110_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0110Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0110Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0110Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0110_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0110LowerBoundTable : List ℤ :=
  [85, 74, 2, 2, 260, -7, 218, 402, 206, 364, 363, 90, 260, 153, 10, 701,
  387, 360, 99, 510, 326, 9, 175, 11, 691]

def fractionalNearFrameSubtreeG3R0110LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0110Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0110LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
