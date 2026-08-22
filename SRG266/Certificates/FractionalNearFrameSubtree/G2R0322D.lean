import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0322`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0322Mask : ℕ := 5390065587574292

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0322Witness : Array ℤ :=
  #[-41, 39, 107, 76, 51, -12, -15, 49, 72, 113, -26, -88, -38, 25, 137, 57,
  53, 19, 93, 69, 89, 53, 128, 68, 36, 74, -7, -96, -26, -125, -41, 73, 79,
  62, -7, -69, -5, 72, 84, -43, -18, 71, -36, -67, 72, -33, 109, 18, -16,
  -50, 48, 93, 20, 7, -104, 39, -109, 67, -21, -42, 99, 161, -88, 2, 118,
  43, 137, 21, 81, -106, -85, 58, -21, -64, -50, -31, -36, -5, -106, 14,
  -22, -40, 14, 71, 31, 46, -29, 1, 24, -64, -54, 135, 51, -11, 65, -93, 79,
  -19, -4, 7, -44, -14, -30, 84, 60, -6, 11, 77, 139, -40, -154, 46, 97, 53,
  -15, -101, 5, 48, 45, -63, 47, 53, 34, -21, 83, -23, 54, -30, 65, 0, -2,
  82, 7, -103, -86, -38, 105, -31, 10, 53, 93, 79, 0, -27, -75, 61, 46, 149,
  63, -47, 139, 54, 193, -100, -45, -69, 0, 30, -52, -1, 50, 114, 13, -49,
  -14, -76, -68, 137]

theorem fractionalNearFrameSubtreeG2R0322_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0322Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0322Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0322Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0322_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0322LowerBoundTable : List ℤ :=
  [155, 205, 5, 265, 2, 184, 286, 234, 2, 300, 394, 301, 177, -43, 551,
  -141, 11, 376, 274, 472, 481, 313, 46, 301, 104]

def fractionalNearFrameSubtreeG2R0322LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0322Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0322LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
