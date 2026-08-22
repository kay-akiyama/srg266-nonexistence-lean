import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0498`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0498Mask : ℕ := 5811371688938648

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0498Witness : Array ℤ :=
  #[7, 161, -92, 11, -1, 17, 66, -65, 45, 3, 4, 122, 15, 126, -18, 179, -57,
  133, -103, 14, 53, 13, -72, 1, 54, 43, 138, -27, -15, -25, -17, -110, -19,
  229, 104, -85, -171, -51, 105, 218, 20, 116, 35, 108, 253, -156, -232,
  -124, 45, 84, 110, -263, -9, 19, -4, -84, 52, -32, 51, 42, 49, -36, 100,
  2, 51, 36, 21, -7, 34, -15, 49, -66, 5, 36, -22, -40, 111, -56, -117, 51,
  82, 96, -86, -50, 40, 9, 14, 147, 5, 7, -78, 84, 36, 32, 53, -156, -30,
  56, 33, 34, -77, 24, 183, 182, 56, 13, 100, 117, 48, -73, 1, -103, -16,
  86, -22, -60, 32, 103, 74, -53, -74, -103, 141, 112, 33, -9, -87, 6, -22,
  86, 127, 49, 8, 52, -10, 29, 20, -33, 134, 37, -70, -33, -39, -14, 64,
  -42, 48, 38, -133, -31, 20, -18, -21, -91, -74, -21, -41, 23, -105, 15, 6,
  59, -4, -18, 13, -105, 12, 42]

theorem fractionalNearFrameSubtreeG2R0498_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0498Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0498Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0498Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0498_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0498LowerBoundTable : List ℤ :=
  [42, -4, 2, 118, 319, 195, 134, 169, 29, 372, 10, 196, -267, 471, 215,
  194, -63, 392, 512, 47, 10, 207, 349, 670, 93]

def fractionalNearFrameSubtreeG2R0498LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0498Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0498LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
