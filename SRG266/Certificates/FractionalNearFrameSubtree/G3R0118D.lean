import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0118`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0118Mask : ℕ := 5389446651910824

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0118Witness : Array ℤ :=
  #[10, -10, 7, -108, 0, 9, -35, -9, -133, -22, 106, 61, 61, 0, 62, -1, 46,
  62, 28, 7, -45, -2, -27, 56, -58, -48, -119, -83, 1, -35, -14, 46, 61,
  106, 30, 44, -64, -101, -34, 18, 124, 5, 5, 25, 2, -36, 117, 31, 34, -12,
  2, -25, -2, 21, 104, 57, -66, -20, 37, -103, -78, 10, -56, -135, -3, 90,
  -49, 47, -16, -6, 63, 71, -26, -35, -92, 32, 97, 72, 18, 91, 25, 78, 37,
  76, -42, 24, 16, -14, -9, -30, -44, 76, 16, 33, 18, -56, 74, 48, -72, -26,
  9, 7, 50, -4, -57, -62, -35, -59, -130, -31, 40, 63, -20, -63, 71, 45, 48,
  40, -39, -64, -53, 35, -122, -66, -35, 25, -83, 7, -123, -78, -19, 60, 48,
  54, 0, 30, 0, 41, -7, 0, -88, -15, -50, 9, 37, 0, 1, 8, -93, -57, -41, -7,
  40, 11, 24, -110, 15, -15, 21, 24, -65, 55, 79, 99, 48, 43, 0, 47]

theorem fractionalNearFrameSubtreeG3R0118_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0118Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0118Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0118Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0118_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0118LowerBoundTable : List ℤ :=
  [-130, -89, 24, 1, 2, 1, 3, -49, 60, -194, 329, -295, -43, 49, 404, -191,
  202, 208, 124, -41, -247, 10, 242, 41, 266]

def fractionalNearFrameSubtreeG3R0118LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0118Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0118LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
