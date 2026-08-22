import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0013`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0013Mask : ℕ := 753839376079377

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0013Witness : Array ℤ :=
  #[28, 17, 14, -66, 0, -90, 140, 12, 32, 12, -16, -61, 75, -37, 36, -104,
  18, -67, -39, -36, -39, -22, -5, 115, 58, 29, 8, 14, -17, -35, -41, 0,
  -46, -43, -20, 0, 25, 109, -39, -12, 12, 29, 18, 5, -82, -81, 15, 15, 73,
  34, 1, -9, 7, 17, 6, 16, -75, 7, -9, 73, -1, 70, 43, 23, -5, 17, 33, 41,
  42, -28, 34, 7, -15, 19, 14, -135, 1, -21, -54, -19, -37, -26, -46, 16,
  -7, 21, -45, -23, -50, -13, -22, -17, -17, -63, 43, -7, 56, -65, 26, -28,
  -52, -40, 45, -8, 12, -105, -17, -93, -57, -76, -101, -70, -52, 233, 113,
  42, 32, 28, -18, -22, 0, 114, 16, 8, -1, -2, -7, 171, 46, 12, -13, 4, 58,
  -81, 95, -38, 5, 31, 49, 0, -28, 14, -6, -4, -47, 67, 15, 161, 6, -10, 35,
  42, 52, 17, 19, -88, -17, -41, 156, 0, 15, -113, -15, -48, 15, -113, -26,
  -31]

theorem fractionalNearFrameSubtreeG3R0013_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0013Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0013Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0013Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0013_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0013LowerBoundTable : List ℤ :=
  [-46, 100, -96, 87, -71, 13, -50, 2, 89, 149, 243, -52, 9, 130, -20, -58,
  -282, 79, 58, -104, 9, 10, -271, 165, 162]

def fractionalNearFrameSubtreeG3R0013LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0013Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0013LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
