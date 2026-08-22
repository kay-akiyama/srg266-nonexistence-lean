import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0149`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0149Mask : ℕ := 14250446602019218

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0149Witness : Array ℤ :=
  #[-110, 98, 2, 16, 52, 38, -31, -16, -18, -98, -4, -46, -94, 4, -84, -5,
  -133, 31, 19, 8, -1, -4, 33, -84, -28, 80, 92, -35, -104, 5, -174, -168,
  -158, 71, 86, 17, 126, 159, 8, -70, -34, 90, 166, 114, 28, -51, 9, 99, 14,
  -69, -85, -19, -33, 43, 54, -19, -29, -23, 26, -21, -49, -45, -33, 11,
  -34, 49, 91, 22, -106, 63, -46, -20, 45, -41, 27, -55, 44, -9, 22, 97, 84,
  -9, -23, -63, -58, 4, -87, -31, 0, 84, 16, 1, -29, 50, -42, 23, 97, 168,
  -11, -31, 97, 2, -78, 16, 13, -65, -60, -41, 5, 42, 82, -29, 54, 1, 6,
  -25, 2, 12, 115, 11, -3, -96, 67, -27, -12, 4, 48, -28, 5, -94, -13, 54,
  44, 47, -34, 2, -85, 9, 3, -14, 23, 59, 6, 68, -75, 59, -2, -64, 0, 13, 9,
  39, 104, -15, -10, 118, -44, 71, 8, 56, 99, -74, 74, -26, -81, -86, 26,
  98]

theorem fractionalNearFrameSubtreeG5R0149_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0149Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0149Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0149Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0149_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0149LowerBoundTable : List ℤ :=
  [-52, 120, 0, 1, 116, 131, -4, -106, -74, 9, 146, -126, 141, 181, -39,
  -83, 154, 106, 157, -71, 157, 178, 251, 115, -239]

def fractionalNearFrameSubtreeG5R0149LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0149Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0149LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
