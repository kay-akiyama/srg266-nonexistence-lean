import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0550`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0550Mask : ℕ := 6839876802253202

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0550Witness : Array ℤ :=
  #[-7, -22, -18, 6, 68, -1, -91, 70, 15, -5, -71, -12, -14, 119, 19, -4,
  13, -12, -7, -10, 37, 99, -32, -1, 58, -57, -25, -37, -45, -4, 2, 35, 5,
  18, 28, -116, 3, 81, 52, 114, 15, -38, 11, -43, -65, -50, -55, -22, 132,
  -33, -36, -20, -26, 19, 95, 105, -16, -48, -36, -12, 116, -47, -7, 18, 74,
  -14, -25, 44, 37, 72, -50, 66, 43, -23, 46, 49, -21, -22, 4, -21, 85, 75,
  56, -8, 100, -29, 19, -79, -61, -16, 109, -61, -26, -55, 31, -68, 5, 31,
  -33, 18, -38, 90, 2, -11, 32, -4, -2, -66, -6, -21, -73, -3, -58, 79, 89,
  60, 0, 73, 125, -43, -41, -53, -35, 5, 69, 72, 90, -54, 90, -1, 23, 20,
  19, -13, 25, -33, -69, -152, 39, 8, 66, -71, 26, -5, 46, -39, 2, 78, -62,
  10, 93, 10, 35, 49, 42, 67, -59, 24, -41, 24, 75, -29, 46, -62, -6, 0,
  -52, -2]

theorem fractionalNearFrameSubtreeG2R0550_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0550Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0550Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0550Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0550_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0550LowerBoundTable : List ℤ :=
  [58, 76, 98, 58, 75, -199, 129, 63, 88, 10, 371, -3, 87, 74, 118, 117,
  273, 156, 24, 305, 9, 195, 145, 165, 11]

def fractionalNearFrameSubtreeG2R0550LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0550Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0550LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
