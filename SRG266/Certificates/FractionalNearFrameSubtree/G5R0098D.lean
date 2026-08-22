import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0098`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0098Mask : ℕ := 5541765754560914

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0098Witness : Array ℤ :=
  #[63, -5, 9, 113, -14, 123, -22, 59, 19, -28, 37, -90, -75, 14, -46, -85,
  48, 17, 12, 90, -51, -18, -2, -52, 0, 38, -6, -40, 15, -22, 0, -111, 128,
  16, 30, 70, 94, 76, -92, -6, -36, 3, -58, 65, 36, 41, 63, -13, 63, -1,
  -70, -21, 42, -47, 24, -31, 42, 60, -33, -6, -49, -44, 22, -77, 15, 13,
  -89, 8, 62, -10, 73, -60, -6, 102, 10, 35, 91, -14, 27, 153, 67, -27, 26,
  -187, -131, -25, -10, -59, 100, -30, 118, -15, 78, 115, 7, -130, 37, 65,
  -102, -45, 76, -111, -33, -11, -123, -37, -26, 47, 5, -17, 55, -32, -71,
  -33, -18, 9, 106, 64, -12, -54, -33, -30, 74, -20, 11, -65, -53, -32, -72,
  -62, -3, -17, 40, 37, -83, 77, -111, 58, 36, 152, -64, -33, 62, 18, 92,
  13, 13, 3, 49, -35, -58, -45, -7, -83, 91, 1, 35, -8, 35, -148, 136, 77,
  17, -24, 68, -22, -65, 100]

theorem fractionalNearFrameSubtreeG5R0098_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0098Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0098Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0098Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0098_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0098LowerBoundTable : List ℤ :=
  [-84, 6, -54, 91, 2, 3, 7, 3, -6, 11, 10, 126, -62, 171, 323, 297, 74, -4,
  101, 9, -10, 299, 209, 55, 58]

def fractionalNearFrameSubtreeG5R0098LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0098Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0098LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
