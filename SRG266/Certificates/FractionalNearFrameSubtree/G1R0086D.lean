import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0086`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0086Mask : ℕ := 931064463343956

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0086Witness : Array ℤ :=
  #[-93, 40, 4, 1, 5, 33, -23, 253, 106, -59, 70, -13, 310, -115, 159, 193,
  -95, 29, -60, 136, 60, -54, 7, -24, 126, -231, 157, 0, -83, 202, 15, 246,
  -100, -48, -68, 127, 39, -371, -159, -58, 307, 189, 60, -10, 206, 53, 19,
  -24, -44, 4, 126, -318, -196, 69, -35, -68, 151, -100, -44, 56, 29, -46,
  446, -90, -15, -23, 47, -24, 163, -55, -165, 150, -202, 148, -157, 163,
  -207, -13, 62, 95, 19, 88, 110, 37, -101, 12, 143, 15, 13, 19, 454, 49,
  -107, -49, -103, 122, -283, 1, 30, 26, -204, 476, 51, -30, -256, 74, 251,
  25, 14, 69, 268, -257, -160, 24, -18, 22, 80, 12, 232, 44, -2, 32, -4, 30,
  -28, 115, 2, 138, 91, 183, 48, -367, 39, 267, 78, -59, 49, -117, 119,
  -111, 139, -60, 387, -7, -183, -69, -110, 90, 24, 0, 515, 105, -77, -120,
  -219, -87, 192, 311, -126, -27, 59, 165, 45, -361, -342, -12, -85, 184]

theorem fractionalNearFrameSubtreeG1R0086_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0086Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0086Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0086Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0086_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0086LowerBoundTable : List ℤ :=
  [146, 221, 47, -183, 546, 358, 380, 3, 389, 15, 615, -163, 490, 10, 979,
  -335, 173, 131, -107, 29, 1007, 714, 206, 544, 438]

def fractionalNearFrameSubtreeG1R0086LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0086Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0086LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
