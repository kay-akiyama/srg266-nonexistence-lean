import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0637`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0637Mask : ℕ := 11344987452458060

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0637Witness : Array ℤ :=
  #[-161, -64, 69, 38, 65, -150, -60, 71, 39, 68, -18, -124, -93, -129, 59,
  43, -145, -74, 27, -64, -42, -92, -34, -6, 62, 13, 41, 81, 54, 50, -49,
  10, 10, -24, 163, 151, -57, -88, -112, 66, 135, 126, -154, 55, 8, 8, 54,
  -21, 81, 138, -64, -121, -110, -46, 201, 95, 105, 51, 53, -159, 69, 86,
  -80, 88, 74, -158, -3, -143, 80, -171, -43, -49, 1, 61, 84, -7, 113, -27,
  16, 6, 2, -62, 75, -31, 109, 10, 16, 15, -64, 88, 46, 2, 35, -72, 0, 76,
  -45, 177, 70, -15, 5, 31, -70, -16, -83, -44, -55, -134, 13, 11, 67, 136,
  49, 4, 37, -24, -55, -44, -24, 135, -33, 79, 39, -16, 38, -114, -105, -46,
  -8, 39, 0, -88, 4, -55, -21, 6, -129, 14, -38, 1, -59, -86, 62, 48, 14,
  -4, 38, 32, -12, 63, 32, 81, 40, -38, 67, -8, 26, 119, 20, 109, 104, 47,
  25, 93, -131, 84, -123, -104]

theorem fractionalNearFrameSubtreeG2R0637_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0637Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0637Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0637Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0637_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0637LowerBoundTable : List ℤ :=
  [-24, 143, 203, 40, -13, 100, 2, -176, -97, -111, 202, 137, 173, 348, 175,
  73, 171, -51, 69, 10, 276, -300, -57, 267, -184]

def fractionalNearFrameSubtreeG2R0637LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0637Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0637LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
