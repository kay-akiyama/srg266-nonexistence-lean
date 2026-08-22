import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0379`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0379Mask : ℕ := 5738159834599826

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0379Witness : Array ℤ :=
  #[17, 5, 7, 30, 0, 45, 0, -14, -62, -124, -36, 124, 93, 175, 2, 63, 37,
  88, 54, 39, -29, 96, 35, -12, 4, -60, -10, -55, -94, -17, -36, -149, -50,
  16, 64, 54, 39, 81, 30, 9, 49, -13, 66, 99, -122, 82, 0, -65, 25, 0, -11,
  121, 46, -49, -76, -35, 70, -26, -30, 103, 24, -36, 162, 75, -25, -118,
  -41, 127, -37, 11, -49, -20, -30, 36, 162, -48, 41, 10, -38, -69, 7, 29,
  61, 13, 43, 43, -19, 71, 90, 45, 82, 91, 81, 7, -11, 6, 41, 101, -3, 54,
  40, 84, 60, 78, -57, 65, -45, -10, 99, 58, -57, -42, -93, -80, 28, -31,
  -12, -73, -114, 36, -7, -58, 17, -103, -16, -48, -107, 95, 49, 44, 19, 58,
  68, 79, 71, 113, 5, -52, 10, 9, -22, 14, 21, -19, 11, 13, -5, 70, 104, 81,
  16, -56, 12, -16, -39, 36, 51, -5, 2, -33, -37, 28, -44, -8, 81, -17, -56,
  35]

theorem fractionalNearFrameSubtreeG2R0379_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0379Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0379Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0379Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0379_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0379LowerBoundTable : List ℤ :=
  [62, 14, 12, 203, 67, 98, 139, 222, 198, 52, 193, -5, -48, 260, 372, 148,
  338, 123, 403, 119, 321, -14, 205, 580, 298]

def fractionalNearFrameSubtreeG2R0379LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0379Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0379LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
