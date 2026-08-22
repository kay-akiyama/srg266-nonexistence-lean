import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0059`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0059Mask : ℕ := 969059149251146

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0059Witness : Array ℤ :=
  #[28, -59, -56, -45, -15, -1, 29, 43, 10, 84, 13, 14, 50, -28, -60, -85,
  47, 17, 43, 34, 21, -35, -73, 23, -26, -46, -11, -5, -16, 71, -65, 52,
  -28, -83, 23, 23, -24, 79, 55, -36, -70, 27, 27, 0, -30, -19, 22, -7, 23,
  -2, -26, -64, -23, 44, -14, -26, 2, -7, -28, 7, 21, 31, 3, 10, 7, 74, -51,
  -25, -56, -15, 0, 39, 44, 53, 2, -25, -18, -31, -1, 11, 15, 37, -4, -54,
  -6, -17, -15, 32, 10, -3, 42, 38, -24, -58, 18, 9, 117, 29, 17, -46, -63,
  30, -9, -2, -13, -15, -3, 26, -32, -34, 9, 59, -23, -19, -50, -38, 40, -4,
  -49, -13, 53, -4, -42, -9, 16, 37, 10, -18, 5, 40, -57, -14, 8, 21, -8,
  -111, 25, 14, 50, 3, -9, -13, -9, -27, 28, 11, -48, 3, 16, 28, 28, -13, 8,
  -12, -75, -47, -84, 30, 36, 58, -25, 73, 20, 44, 77, 13, -12, -82]

theorem fractionalNearFrameSubtreeG3R0059_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0059Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0059Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0059Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0059_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0059LowerBoundTable : List ℤ :=
  [-75, 9, 2, -72, -34, 2, 37, -84, 22, -109, 68, 11, 81, 149, 126, -137,
  86, 184, 9, 64, -121, -124, -55, 121, -28]

def fractionalNearFrameSubtreeG3R0059LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0059Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0059LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
