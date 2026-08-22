import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0472`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0472Mask : ℕ := 5809421925620376

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0472Witness : Array ℤ :=
  #[-46, 32, -45, 65, -7, 10, -63, -1, 4, -39, 42, 57, 68, 104, -49, 0,
  -117, 50, -10, 85, 1, 109, 19, 65, 7, -99, -1, -19, -91, -62, 74, -8, 7,
  -2, 8, -37, 10, 64, 23, 25, 15, -103, 124, -22, 7, -48, -95, -37, -89, 49,
  20, 76, 17, -57, 0, -41, 59, -4, 0, -34, 16, 69, -37, -75, 35, -10, -68,
  -1, -25, 13, -12, 115, 123, 4, 114, 1, 161, 8, -40, 8, -55, -23, 15, -20,
  -1, 19, 5, 13, 68, 31, 53, 21, -55, 45, 17, 118, 101, -16, -102, -2, 73,
  11, -51, 52, 63, 10, 0, 46, 1, 50, 11, 59, -21, -41, -33, 86, 26, 91, 34,
  53, 4, 91, 41, -4, 124, -47, -41, -1, 61, 15, 73, 54, 7, -18, -113, 45,
  12, -32, 27, 20, -52, 7, 85, 20, -45, 36, 19, 77, -8, -31, -4, 92, 37, 76,
  -17, 49, 26, 110, 49, -24, 46, -44, -10, 87, 52, 43, -6, -29]

theorem fractionalNearFrameSubtreeG2R0472_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0472Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0472Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0472Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0472_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0472LowerBoundTable : List ℤ :=
  [87, 210, 185, 205, 206, 89, 7, 73, 115, 631, 11, 143, 402, 426, 315, 10,
  34, 251, 173, 210, 200, 311, -72, 197, -16]

def fractionalNearFrameSubtreeG2R0472LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0472Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0472LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
