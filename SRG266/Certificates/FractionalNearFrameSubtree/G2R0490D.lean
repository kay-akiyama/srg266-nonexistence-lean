import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0490`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0490Mask : ℕ := 5811178549237260

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0490Witness : Array ℤ :=
  #[-11, 59, 19, -93, 92, -78, 60, -49, 60, -25, -140, -20, 67, 9, -109,
  -31, 31, 106, 39, -10, 34, -21, -83, 42, 13, -135, -18, -56, -11, -1, 41,
  31, 28, -102, 84, 25, -10, -18, -58, -47, 164, 64, 4, -11, 86, 143, 157,
  -140, 1, -81, 68, 97, 130, -194, -2, 57, 95, 12, 82, -95, -140, 109, -82,
  139, -3, -78, 57, 65, -59, 215, 203, -76, -56, 100, 175, -38, -95, -23,
  -1, 93, 82, 90, 33, -73, 155, -1, -65, 85, 162, -68, 26, 54, -210, -24,
  -12, -163, -5, 29, -16, -38, -39, 7, -98, 28, 2, -11, 62, -215, 7, -10,
  90, 22, 168, 99, -4, -103, 79, 95, 49, 195, 21, -136, 53, 114, -104, -60,
  36, 96, 32, 85, 75, -24, 84, -9, 61, -101, -16, 81, -6, -106, 50, -7, -39,
  56, 65, 36, 238, 151, 106, 52, 110, 78, -6, 105, 83, 64, 83, 105, -66, -8,
  -119, 73, -96, 87, 8, -1, 144, 101]

theorem fractionalNearFrameSubtreeG2R0490_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0490Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0490Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0490Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0490_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0490LowerBoundTable : List ℤ :=
  [152, 411, 269, 235, 48, 70, 45, 226, 6, 327, 884, 432, 97, 452, 246, 96,
  272, 303, 297, 168, 8, 517, -137, 94, 626]

def fractionalNearFrameSubtreeG2R0490LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0490Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0490LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
