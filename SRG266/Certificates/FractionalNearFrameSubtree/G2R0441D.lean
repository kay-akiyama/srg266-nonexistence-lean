import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0441`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0441Mask : ℕ := 5786357548501656

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0441Witness : Array ℤ :=
  #[22, -19, -14, -42, 1, 16, -12, -20, 29, -30, 12, 68, -13, 56, 23, 0,
  -32, 17, -9, -5, -12, 5, -88, -27, 45, 19, 61, 76, 70, 6, 39, 11, 12, -89,
  -75, 17, 44, 38, -20, -51, 36, 48, -5, -44, -31, 33, 28, 126, 28, 0, 13,
  86, -14, -23, -10, 47, 50, 41, -6, -102, 135, 43, -94, 83, 34, -87, 33,
  -52, 67, -71, -44, -18, 83, 32, 45, -47, 15, 8, -45, -13, -30, -8, 58, 16,
  -23, -16, 21, 56, -12, -22, 4, 8, -55, 67, 62, -30, 11, -23, -1, 36, -51,
  -5, 42, -1, 26, -39, 53, -44, 35, 9, -32, -3, 22, -21, 8, 27, 29, 40, 24,
  -27, 32, -36, -24, -2, -22, 70, -79, 34, 35, -21, 27, -50, 48, 36, 20, 95,
  -74, 146, 86, -29, 45, 31, 27, 31, 13, 7, -55, 15, -7, -6, 84, -23, 43,
  -76, 6, -15, -94, 76, -38, -51, -26, -2, -57, -50, -53, -28, -29, 6]

theorem fractionalNearFrameSubtreeG2R0441_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0441Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0441Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0441Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0441_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0441LowerBoundTable : List ℤ :=
  [14, -17, 2, 69, 125, 1, 128, 56, 51, 10, 199, 286, -134, 0, 188, 102,
  273, 68, 75, -74, 195, 53, 50, 38, 38]

def fractionalNearFrameSubtreeG2R0441LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0441Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0441LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
