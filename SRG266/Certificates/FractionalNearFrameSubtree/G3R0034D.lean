import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0034`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0034Mask : ℕ := 954028476960266

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0034Witness : Array ℤ :=
  #[37, 114, 49, 42, 9, 46, 6, 32, -4, 110, 5, -25, -12, -84, 6, -112, -22,
  41, -1, 3, -28, 34, -18, -88, -51, -78, 59, 56, 60, 32, 90, 69, -53, -51,
  65, -95, -56, 8, -10, 8, 89, -17, 54, 7, 96, -6, 44, 60, 79, 6, -87, -30,
  -109, 4, -11, 47, -10, 0, 40, 28, 85, 11, 2, -1, -28, 49, -4, -19, 12,
  -111, 19, 55, -77, 17, -75, 24, -49, 33, -1, 59, 0, 16, 46, 44, 7, 51,
  -22, 2, -10, 63, 12, 14, 31, 2, 10, 28, 52, 18, -34, -1, 56, -43, -4, 50,
  31, 147, 53, -12, -35, 1, -12, 121, -57, -102, -11, 24, 35, 45, 64, 31, 7,
  62, 15, 57, 71, 65, 39, -7, 91, 143, 0, 48, -23, 56, 43, 54, -21, -58, 23,
  -4, 82, -48, 75, -87, 45, -100, -62, -12, 83, 28, 12, 46, -56, -25, 94, 0,
  -3, -20, -59, 44, -3, 48, 52, 76, 43, 9, 28, 45]

theorem fractionalNearFrameSubtreeG3R0034_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0034Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0034Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0034Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0034_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0034LowerBoundTable : List ℤ :=
  [125, 262, 82, 66, 63, 1, 363, 245, 49, 178, 502, 120, 123, 230, 178, 112,
  266, -1, 98, 110, 183, 83, 430, 176, 209]

def fractionalNearFrameSubtreeG3R0034LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0034Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0034LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
