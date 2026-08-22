import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0405`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0405Mask : ℕ := 5741428750115240

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0405Witness : Array ℤ :=
  #[-59, -105, -97, -65, 39, 20, 211, 26, 115, 75, 16, 0, -80, 25, -92, 35,
  47, -27, 101, -71, 133, -182, -74, -51, -3, -32, 168, 116, -66, -114, 96,
  -93, 119, 55, 120, -6, -71, 35, 102, 91, -64, -24, -35, 138, 75, 181, -90,
  -144, 85, 82, 63, 61, -44, -186, -8, 112, 110, -61, -57, -47, -15, 82,
  -61, 44, -100, -125, 3, -170, 68, 190, 20, 10, -5, -54, -70, -44, 77, 19,
  -7, -30, 117, 134, 51, 141, 0, -3, 218, -113, -65, -57, -51, -27, -56,
  -25, -64, 40, -83, -118, -86, -39, 0, -7, -16, 5, -84, -21, -172, -14, 10,
  -99, -45, -205, 9, 101, 99, 52, 60, 108, -46, 28, -124, -122, 108, -83, 4,
  53, 81, 63, 88, 5, 23, -31, -11, 19, 87, 126, 85, 15, 114, 47, -65, 32,
  -19, 35, 15, 90, -7, 21, 103, 50, 73, 62, 116, -30, 19, -67, -111, 3, -36,
  41, 13, 3, 83, 154, 111, 37, -37, -1]

theorem fractionalNearFrameSubtreeG2R0405_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0405Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0405Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0405Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0405_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0405LowerBoundTable : List ℤ :=
  [-1, 247, -41, -49, 307, 14, -141, -87, 148, 173, 344, 406, 251, 354, 318,
  9, -103, 130, -134, -131, -165, 277, 608, 646, 87]

def fractionalNearFrameSubtreeG2R0405LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0405Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0405LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
