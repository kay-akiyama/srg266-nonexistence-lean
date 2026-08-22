import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0018`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0018Mask : ℕ := 883725325537795

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0018Witness : Array ℤ :=
  #[-50, -36, -13, 0, 17, 27, 64, 96, 34, 13, 68, 59, -58, -12, 0, -83, -40,
  27, 56, -31, 88, 30, -51, 70, -54, -10, -91, -51, -55, 114, -44, 59, 33,
  61, 82, -53, -16, -18, 113, -44, -38, 19, 123, 87, 119, -29, -53, 98, -5,
  82, -86, -112, 11, 47, -48, 65, 19, -26, 32, -27, 76, 37, -45, 22, 68, 25,
  21, 4, -64, 55, 44, -1, 22, 113, 89, -66, -91, -43, -9, -28, 65, 11, 3,
  -9, 12, 10, 61, 18, -36, -29, -67, -6, -36, 85, 68, 30, 66, 37, 12, -34,
  32, -10, -25, 10, -16, -29, 22, -29, 45, 27, 6, 26, 60, -13, 28, 61, -75,
  -12, -70, -106, -72, 111, 82, -36, -8, -12, -35, -80, -53, 51, 51, -12,
  38, 15, -8, 14, -28, -17, 62, -47, -1, 17, 13, 4, 34, 54, 32, -34, -57,
  61, 12, 6, -87, -4, -39, 47, 0, 32, -20, 27, 40, 53, -32, -31, -20, -41,
  35, -7]

theorem fractionalNearFrameSubtreeG3R0018_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0018Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0018Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0018Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0018_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0018LowerBoundTable : List ℤ :=
  [21, 2, 55, 10, 2, 158, 146, 88, -16, 103, 205, 198, -42, 118, 269, 265,
  191, 0, 24, 9, 101, 200, 189, 319, 7]

def fractionalNearFrameSubtreeG3R0018LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0018Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0018LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
