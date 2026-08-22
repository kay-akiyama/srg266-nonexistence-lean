import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0093`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0093Mask : ℕ := 2511545647940242

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0093Witness : Array ℤ :=
  #[60, 79, 62, 90, 105, 21, -11, 52, 52, -25, -13, -3, -22, -74, -68, -81,
  -9, -9, -10, 15, -6, 14, -20, 20, 0, -5, 77, 15, 47, 0, 50, 29, 37, 24,
  -5, -49, -34, 7, -84, -24, 14, -1, 7, -17, 53, -6, 48, 15, -20, -10, 11,
  48, -24, -45, -30, 6, 7, -2, 62, 38, 0, -31, 43, -18, 23, 32, -13, -32,
  -27, -1, -25, 22, -2, 37, -48, 32, 69, 50, -64, -30, 20, -11, -18, 53,
  -16, -44, -80, -19, 69, 5, -17, -22, 60, -23, -14, -21, -67, 57, -14, -5,
  1, -4, 23, 10, 4, 6, 24, 27, 23, -10, 35, -25, -23, 6, -86, -35, 7, -12,
  -61, -24, -26, -35, -52, 60, 28, 14, 22, -34, -13, 60, 23, -59, 93, -71,
  -2, 38, 23, -72, -20, 18, -5, 6, -37, 9, 5, 6, 38, 40, 2, 3, 61, -22, -69,
  -30, 47, -60, -6, 0, 0, -73, 43, 31, 20, -7, 72, 78, -27, 12]

theorem fractionalNearFrameSubtreeG3R0093_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0093Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0093Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0093Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0093_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0093LowerBoundTable : List ℤ :=
  [-29, 2, 13, -23, -65, 90, 23, 53, 2, 130, -19, 72, 211, 15, -1, 70, 77,
  11, 9, 10, 134, 76, -18, 151, 252]

def fractionalNearFrameSubtreeG3R0093LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0093Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0093LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
