import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0334`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0334Mask : ℕ := 5638211692338185

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0334Witness : Array ℤ :=
  #[200, 65, 45, 41, 20, -83, 0, -49, -31, 51, -66, -168, 76, -19, -17, 119,
  -47, -34, -5, 160, -42, 60, -61, -34, 14, -46, -56, -82, 60, 95, 70, 98,
  116, 6, -110, 55, -116, 90, 61, -72, 18, -80, 57, -86, 54, 153, 86, 3, -9,
  40, -69, -86, -127, -87, -48, -84, -92, -126, -20, -6, -38, 89, 9, -14, 9,
  38, 11, 19, -7, 23, 40, 23, 47, 77, 85, 16, -26, -32, 4, 25, 50, 48, 43,
  109, 22, -78, -45, 33, -80, -82, 0, -62, 14, -84, 15, -41, 30, -19, 7,
  -126, 64, 44, -49, 33, 35, 10, 56, 68, 34, 47, 3, 62, 26, 52, 21, 105,
  -10, -20, -20, 0, 27, 46, 32, -83, 10, -33, 0, -79, -35, -57, -13, -27,
  56, -12, 31, -17, 14, 15, 64, 5, -84, 78, 86, -34, 48, 9, 35, 28, 80, 37,
  65, 72, 96, 37, 70, -74, -104, -21, -45, -42, 58, -19, -40, -16, -77, -3,
  17, -6]

theorem fractionalNearFrameSubtreeG2R0334_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0334Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0334Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0334Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0334_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0334LowerBoundTable : List ℤ :=
  [-35, 69, -137, 106, -20, -117, 2, 214, 190, 258, 255, -24, 11, 249, -145,
  -125, -140, 201, 9, 182, 137, 172, 379, -16, 290]

def fractionalNearFrameSubtreeG2R0334LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0334Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0334LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
