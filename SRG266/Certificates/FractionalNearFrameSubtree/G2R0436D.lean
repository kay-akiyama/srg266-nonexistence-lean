import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0436`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0436Mask : ℕ := 5785407607510104

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0436Witness : Array ℤ :=
  #[-28, 26, 56, 49, -7, -70, 52, -249, -21, -3, -15, 54, 15, 109, 206, 136,
  52, 7, 112, 47, -223, 71, 14, -17, -30, -2, 0, 40, 8, 88, 20, -70, -77,
  40, 144, 24, -89, 65, -104, 82, 0, -8, -136, -3, 42, -98, 154, -5, 132,
  136, 8, 2, 144, -65, 36, -14, -193, 204, 22, -74, 82, -133, 32, -58, -12,
  137, 29, -39, -55, -111, 50, -13, 25, -52, 45, 37, -15, -115, -22, 9, -7,
  -69, 87, 115, -121, -61, 36, 44, -88, 37, -83, -62, 23, 162, -28, 150, -4,
  -31, 68, 191, 113, -60, 153, 89, 138, -83, 131, 0, -14, -149, 100, 8, -19,
  76, 161, 46, 116, -135, 20, 82, -106, -200, -104, 280, 313, -16, 26, 252,
  -48, 78, -23, 69, -31, -116, -103, -95, 113, 158, -93, 202, -29, 106, -15,
  -88, -1, 78, 185, -34, 100, 20, -29, -38, 16, 38, 16, 27, 41, 52, -6, -5,
  -14, -26, 98, -122, 131, -92, 0, -87]

theorem fractionalNearFrameSubtreeG2R0436_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0436Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0436Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0436Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0436_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0436LowerBoundTable : List ℤ :=
  [145, 227, 2, -46, 341, 325, 356, 2, 141, 236, 821, 447, -139, 458, -70,
  39, 420, 175, -32, -213, 10, 524, 38, 481, 425]

def fractionalNearFrameSubtreeG2R0436LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0436Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0436LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
