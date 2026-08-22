import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0145`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0145Mask : ℕ := 1370581395423464

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0145Witness : Array ℤ :=
  #[35, 41, -21, 58, 1, 32, 43, 56, -13, -5, -15, -66, -110, -25, 25, -38,
  -3, -4, -61, 38, 14, 22, 46, -42, 13, -1, -69, 30, -22, -25, -39, 17, -5,
  -29, -14, -22, 32, -69, -3, 0, -21, -17, -1, -1, 26, 1, 16, 17, 13, 21,
  -40, -10, -2, -2, -28, -59, -56, 14, -26, 3, -2, 28, -12, -24, 32, -23, 5,
  -8, 70, 61, 31, -48, 48, -45, -39, 37, 47, -5, 15, 39, 37, 81, -60, 22, 0,
  22, 65, 34, 42, -2, -60, 36, -30, -12, 0, -7, -57, 7, -47, 15, -74, 51,
  -18, 26, -13, -17, -24, -10, -40, 32, 36, -31, 0, 15, 28, -31, -13, 9,
  -12, 25, 9, 23, 14, -32, 68, -26, -14, -12, 11, -55, 41, -30, 37, 31, 32,
  9, 45, 60, -37, 16, -25, 70, -32, 87, 20, -24, -35, 15, -51, 49, -48, 58,
  6, -50, 32, 43, -5, 40, 66, 63, 37, -15, 17, -92, 56, 36, 74, 17]

theorem fractionalNearFrameSubtreeG2R0145_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0145Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0145Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0145Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0145_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0145LowerBoundTable : List ℤ :=
  [-34, 137, -15, 2, 64, -57, 18, 39, 1, 95, -37, 288, -31, 111, -33, 153,
  -234, 198, 48, 153, 82, 58, 305, 25, 10]

def fractionalNearFrameSubtreeG2R0145LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0145Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0145LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
