import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0559`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0559Mask : ℕ := 6841870979796056

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0559Witness : Array ℤ :=
  #[87, 27, 72, -24, 23, 0, 0, -25, -4, -9, 22, -43, 10, 1, 34, 40, 42, 11,
  -50, 46, 16, 47, -31, -102, -4, 0, -20, -80, 52, 4, 140, 106, -179, -77,
  36, -9, -17, -75, 28, 23, 13, -35, 67, 6, 55, -86, -113, 21, 120, 12, -54,
  -90, -51, 22, 146, 131, -137, 91, 31, -11, -185, 88, 22, -84, -166, 21,
  -9, 42, 0, 0, -79, 103, 58, -41, -86, -35, -55, 48, -28, 7, -47, -62, -2,
  18, -44, 18, -12, 136, 30, -29, 68, -158, 6, 59, -95, 1, 15, -17, 80,
  -129, -98, -9, -5, -100, -156, 2, 22, 36, 33, -78, -23, 41, 0, 137, 32,
  28, 38, -35, -74, -41, 85, 29, -47, -31, 45, -47, 7, -13, -86, -158, -7,
  32, 25, 47, 36, -34, -5, -6, 22, 39, 2, -94, 118, -6, 89, -52, 16, 104,
  64, -69, 202, -61, 39, -69, 29, -28, 25, 73, 7, 46, 64, -106, 29, -48,
  -51, -84, -3, -132]

theorem fractionalNearFrameSubtreeG2R0559_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0559Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0559Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0559Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0559_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0559LowerBoundTable : List ℤ :=
  [-113, -15, -149, 2, -37, -153, -92, 80, 1, -86, 147, 51, -16, -369, -13,
  118, 133, -145, 97, 73, 44, 57, -43, -62, 155]

def fractionalNearFrameSubtreeG2R0559LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0559Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0559LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
