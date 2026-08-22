import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0021`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0021Mask : ℕ := 1077024575652166

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0021Witness : Array ℤ :=
  #[7, 49, 50, 73, 25, 109, 149, -14, -8, -22, 0, -4, -146, -128, -144, 0,
  -17, -47, -84, -171, -70, 62, 136, 5, -9, -77, -107, 145, 172, 96, 93, 33,
  27, 95, -59, 95, 21, 31, 89, -62, 103, 9, 138, -88, -136, -131, -127, -22,
  66, -18, -5, -79, 33, 178, 95, 52, -31, 21, 107, -20, 86, 73, -118, 50,
  23, 18, -88, -36, 22, 14, -129, -60, 13, -79, 61, -7, 17, -3, -83, -22,
  27, 174, 54, 104, -59, -10, -17, 40, 47, -8, 6, 26, -1, 11, 33, -6, 81,
  -29, -17, -24, 35, -34, 36, 7, 40, 28, 47, 36, 20, -52, 11, 20, -37, -78,
  20, 5, 25, 108, 35, 0, 9, -72, 57, -129, -60, 12, 56, 44, 72, 17, 57, 3,
  30, -32, -62, -3, -80, 44, -137, -139, 118, 55, -65, -68, 2, 73, 8, 52, 2,
  87, 69, -14, 25, -15, -49, -14, 10, -47, -17, -117, 32, -17, 0, -83, 1,
  86, -15, 55]

theorem fractionalNearFrameSubtreeG5R0021_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0021Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0021Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0021Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0021_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0021LowerBoundTable : List ℤ :=
  [-43, -18, 2, -97, 118, 160, 83, 1, 153, 17, 317, -67, -80, 112, 82, 202,
  -225, 107, 10, 148, 54, 193, 251, 219, 305]

def fractionalNearFrameSubtreeG5R0021LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0021Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0021LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
