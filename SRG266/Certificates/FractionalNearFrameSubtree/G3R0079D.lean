import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0079`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0079Mask : ℕ := 2365526457043985

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0079Witness : Array ℤ :=
  #[81, 191, 31, 119, 214, 6, -15, -6, -215, -104, -44, -67, -13, -4, -68,
  -20, -20, 10, 21, -73, 68, -93, -147, 54, 66, -21, -180, -74, 137, 105,
  113, 40, -108, -36, -54, 125, -18, 117, 124, 96, -43, -52, -67, -123, 137,
  -10, -74, -20, 32, 78, 14, 1, 70, 30, 38, 6, 84, 44, 134, -5, -104, 83, 0,
  -85, -59, 8, 5, -139, -104, -14, 8, -1, 13, 42, 31, 42, -14, 43, -32, 52,
  45, 38, 17, 24, 26, 18, 23, -4, -93, -71, 52, -5, -108, -97, 9, 2, 28,
  -99, -79, 32, 98, 81, -16, 90, 26, -16, 0, 45, 38, -78, -44, 16, 100, 13,
  47, 67, 10, -7, 5, 15, -16, 49, -77, -13, 136, 87, -17, -37, -83, -22, 68,
  53, 8, -117, 1, 13, 88, 71, 137, -1, 26, 93, 81, 41, 24, -49, 63, -18,
  -105, -5, 43, 73, 38, 74, -98, 51, 196, 16, 16, -6, 125, 30, -35, -4, -43,
  55, -5, 49]

theorem fractionalNearFrameSubtreeG3R0079_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0079Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0079Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0079Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0079_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0079LowerBoundTable : List ℤ :=
  [57, 202, 26, 2, 1, 178, 146, 62, 169, 141, 229, 321, 540, 43, 35, 196,
  -89, 153, 128, 130, -77, 441, 1, 382, 185]

def fractionalNearFrameSubtreeG3R0079LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0079Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0079LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
