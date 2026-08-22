import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0180`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0180Mask : ℕ := 6865892009558802

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0180Witness : Array ℤ :=
  #[-15, -32, -37, -14, 102, -36, 51, 45, -22, -12, 24, -3, -7, 10, -29,
  -93, 30, -16, 50, 53, 87, -63, 33, 1, -21, -38, -18, -69, -14, 34, 0, -18,
  18, 27, 10, -23, 14, 6, 40, -8, -45, 101, -112, 1, 19, 5, -3, 58, -85,
  -70, 56, 50, -31, -7, -106, 60, 68, -75, -46, -12, 31, -21, -49, -45, 69,
  35, 47, 27, 49, -31, 44, -86, 16, 84, 52, -87, 21, 0, 44, 32, -51, 39, 4,
  -46, 20, 16, -54, 69, -2, 75, -42, -98, 17, 40, -86, 64, -4, -48, -51, 37,
  -41, 95, -22, -60, 54, 23, -158, 57, 70, 7, -52, -51, -36, 0, -24, -13,
  105, 0, 121, 21, 57, 73, -47, -60, -22, 35, -33, 13, 11, 12, 55, 57, -45,
  9, -10, -24, -50, 21, -50, -64, -98, -29, -12, 29, 43, 48, 10, 3, 39, 34,
  -2, 27, 60, 47, -61, -53, 36, -13, -30, -67, 22, -8, 93, 67, 32, -85, -29,
  34]

theorem fractionalNearFrameSubtreeG3R0180_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0180Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0180Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0180Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0180_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0180LowerBoundTable : List ℤ :=
  [-44, -13, 2, -55, 142, -8, 30, 18, 1, -179, 109, 229, -215, 119, 74, -72,
  130, 223, 64, -246, 60, 285, -77, 9, 9]

def fractionalNearFrameSubtreeG3R0180LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0180Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0180LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
