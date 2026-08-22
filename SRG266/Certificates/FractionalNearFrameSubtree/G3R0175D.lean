import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0175`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0175Mask : ℕ := 6864994342677656

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0175Witness : Array ℤ :=
  #[-13, 48, 36, 5, -37, 20, 80, 5, 88, 11, -63, -29, -69, -88, -9, -10, 29,
  -59, 14, -4, 50, 4, 117, 30, -27, -37, -34, -12, -61, -81, 18, 76, -23,
  18, 46, 40, 74, -52, 6, -72, -18, -105, -23, -18, -9, -6, 59, 59, -4, 30,
  101, -11, -17, 103, 2, 56, -20, -36, 5, 8, -83, -37, 24, -110, -10, 36,
  -51, 51, 33, 99, -37, 25, -14, 9, 55, 98, -52, -10, 40, 8, 57, 61, -1, 59,
  14, 10, 39, -19, -6, 30, 50, -28, 67, -47, 18, 12, -34, 8, -78, -64, 1,
  38, 66, 31, -40, -27, -107, 49, -50, -15, -82, 76, -42, 68, 69, 64, 88,
  164, 56, 22, -62, -66, -16, 4, -23, 8, 2, -20, -27, -64, 39, 40, 8, -27,
  -22, 23, 40, -32, -86, -77, -42, -3, -39, -25, -28, -25, 10, 2, 62, -61,
  5, -94, 9, -27, 20, 147, 24, 50, -21, 9, 105, 21, -21, -38, -33, 43, 89,
  82]

theorem fractionalNearFrameSubtreeG3R0175_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0175Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0175Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0175Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0175_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0175LowerBoundTable : List ℤ :=
  [-32, 3, 63, 44, 2, 1, 74, 51, -3, 306, 24, -236, 166, 181, 52, 222, -46,
  11, 63, 174, 135, 302, 202, 76, 97]

def fractionalNearFrameSubtreeG3R0175LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0175Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0175LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
