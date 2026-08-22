import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0137`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0137Mask : ℕ := 6839909610066578

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0137Witness : Array ℤ :=
  #[-107, -2, -60, 50, -137, -45, 66, -68, 50, 198, 18, 0, -89, -13, 117,
  90, -106, 138, -51, 5, -57, 41, -35, -118, -51, 157, -29, -36, 100, 194,
  30, -82, 3, -9, -129, 27, -38, 18, -29, 86, 72, -68, 13, 99, 64, -35, -45,
  -117, 53, -8, -160, -52, -31, -69, 102, 96, 84, -172, -91, -79, 72, -58,
  -36, -44, 53, 174, 28, -28, 98, 39, -34, -4, -16, -27, 86, -59, -18, -29,
  -51, 132, -40, -24, 39, 107, -63, -119, 97, -15, 29, 27, 104, 156, 130,
  89, 176, 81, 44, -99, 86, 4, 40, -10, 68, 160, 74, -1, -32, 81, 21, -96,
  -46, 0, 51, -54, -95, -4, 106, 61, 120, 215, 136, -23, -59, 0, 65, -192,
  -78, -8, 157, 40, 58, 100, 110, 58, 89, -30, 46, 14, -55, 98, 32, -42,
  -75, -4, 59, -25, 51, 12, 146, 55, -79, 78, -143, 112, -81, 24, -137, 6,
  65, -56, 0, 11, 11, -101, 42, -125, -44, -12]

theorem fractionalNearFrameSubtreeG3R0137_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0137Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0137Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0137Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0137_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0137LowerBoundTable : List ℤ :=
  [7, 88, 121, 376, 0, 1, 3, -63, 2, 287, 351, 92, 240, 372, 286, 124, 151,
  448, 388, 602, 771, 179, -230, -46, 10]

def fractionalNearFrameSubtreeG3R0137LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0137Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0137LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
