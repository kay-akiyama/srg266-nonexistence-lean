import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0057`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0057Mask : ℕ := 4955139575820433

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0057Witness : Array ℤ :=
  #[-76, -110, -5, 26, -97, -105, 90, 25, 113, 43, 16, -65, -72, 83, -25,
  -2, 87, 11, 23, 131, -43, 23, 3, 18, 17, -31, 0, -139, -21, -43, 50, 39,
  11, -9, -1, -22, 38, -9, -134, -93, 57, -101, 65, -77, -80, 66, 42, 35,
  71, -23, -63, -68, 60, -79, -96, -3, -20, 47, 28, 18, -3, -6, 40, 36, 37,
  -22, 5, -8, -67, 27, 17, 24, -46, -49, 13, -54, -78, 96, -26, 7, 46, 4, 8,
  24, -145, 30, 59, -35, -40, -21, -4, -23, -4, 37, -16, 65, 89, -13, 53,
  -10, -19, -25, 7, 38, 44, 36, 0, 19, 29, -18, -35, 60, -67, -57, -29, -45,
  9, 19, -79, -24, 69, 72, -49, -80, 122, -28, 101, -19, 34, 5, 104, 37, 0,
  -14, -36, -22, -20, -21, 3, -103, -52, 73, 0, -8, 110, -54, 105, 9, 89,
  -50, -3, 91, 68, 108, -46, -14, 6, 19, 134, -56, 167, 35, 27, 18, 20, 127,
  101, -7]

theorem fractionalNearFrameSubtreeG5R0057_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0057Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0057Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0057Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0057_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0057LowerBoundTable : List ℤ :=
  [-23, 214, 80, 90, -67, 2, 39, 1, 40, 433, 10, 162, 202, 293, 32, -254,
  103, -11, 248, 87, -278, 89, -217, 1, 309]

def fractionalNearFrameSubtreeG5R0057LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0057Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0057LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
