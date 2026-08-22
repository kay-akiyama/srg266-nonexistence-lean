import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0062`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0062Mask : ℕ := 4980129037725841

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0062Witness : Array ℤ :=
  #[62, 122, 103, 139, 153, 66, -90, 19, -46, 0, -115, -117, -27, -114, -88,
  -65, -181, -72, 23, -89, 6, -202, -126, -123, -53, -35, 37, 69, 180, 252,
  -46, -5, -108, -74, 88, -2, 85, 34, -31, 61, 22, -66, 59, 264, 188, -43,
  31, 5, 112, -3, 45, -203, -33, 18, 68, 116, 202, 11, 119, 57, -26, -120,
  34, -1, -85, -289, -35, -24, 91, -23, 69, -10, 138, 236, -19, -9, -8, -61,
  -57, 34, -35, 33, 91, 224, 48, 72, 134, 91, -54, 83, -42, 173, 33, 86,
  148, -17, 54, -40, -50, -103, -242, 17, 3, 44, 118, 86, 78, 48, 22, -66,
  72, 162, -12, -49, 44, -12, 2, 57, 66, 120, 69, -25, 198, -21, 90, 27, -7,
  104, 69, 76, 90, 0, 42, 200, -58, 225, -100, 54, -292, -102, 104, -296,
  163, 38, -281, -149, 14, 118, 210, 46, -38, 51, -28, 44, -90, 15, 24, 0,
  -112, -125, -51, -17, 38, -89, -44, 121, -154, -46]

theorem fractionalNearFrameSubtreeG5R0062_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0062Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0062Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0062Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0062_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0062LowerBoundTable : List ℤ :=
  [32, 2, 313, 257, 120, -221, 98, 230, 2, 168, -309, 365, 186, 633, 10,
  590, 63, 636, 10, 495, 153, 487, 135, 344, 10]

def fractionalNearFrameSubtreeG5R0062LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0062Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0062LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
