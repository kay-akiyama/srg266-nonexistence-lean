import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0127`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0127Mask : ℕ := 1352171169452682

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0127Witness : Array ℤ :=
  #[-4, 8, -6, 16, 100, 16, 19, -1, -63, 0, 40, -66, -21, -36, -190, -16,
  -25, -17, -37, -42, -47, 0, -33, -4, -36, -15, 27, 82, 19, 64, -46, -105,
  -65, 1, 83, 15, 41, 65, 9, 39, -33, 7, -87, -16, -66, -33, 35, 89, 46,
  104, -74, 25, -91, 96, -33, 2, -38, 49, 0, 45, 93, 4, 66, -62, 6, -61, 82,
  -3, 3, -62, -85, 99, 112, -7, 67, 73, 51, -20, -1, 67, 61, -12, -64, 7,
  54, 12, 124, 48, 88, 40, 6, -60, -12, -14, -13, -27, 60, 45, 122, -10,
  -16, 79, -22, 95, 47, 3, -32, -54, 33, -5, 10, -38, 41, -86, -18, -47, 37,
  -88, 75, -5, -6, -26, 4, -41, -51, 35, 30, 40, -64, 37, -27, 28, -23, 31,
  -34, 85, 62, 24, -60, -11, -1, 4, 53, 53, -90, 86, 9, -44, 4, 43, 78, 26,
  64, 27, -69, -30, 113, 39, 86, -47, 40, 14, 55, 20, 43, 92, -1, 29]

theorem fractionalNearFrameSubtreeG2R0127_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0127Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0127Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0127Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0127_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0127LowerBoundTable : List ℤ :=
  [30, 146, 144, 115, 84, 72, 2, 44, 17, 7, 180, 1, 39, 297, 192, -44, 56,
  280, 360, 249, -123, 512, 234, 143, 100]

def fractionalNearFrameSubtreeG2R0127LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0127Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0127LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
