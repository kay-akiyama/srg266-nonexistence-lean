import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0101`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0101Mask : ℕ := 1252737407247369

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0101Witness : Array ℤ :=
  #[117, -14, 7, 55, -55, -1, -91, -107, -67, -122, 14, -75, 102, 83, 112,
  78, -39, 36, 11, 144, 14, 91, -29, 6, -40, 26, -82, -80, -26, -51, -62,
  -43, 67, 20, 30, -66, -14, -37, -11, 69, 25, -10, 57, 54, 10, 37, 14, 104,
  -14, -11, -47, -117, -108, 27, -68, -46, -90, 25, 24, -17, -110, 102, -8,
  41, 31, 7, -35, 131, -8, -3, -1, -118, 2, -11, 0, -12, 36, -12, 23, -80,
  -55, -34, -13, -59, 32, -33, -51, 45, -34, 74, -24, -38, -2, 80, 5, 51, 4,
  -15, 10, 9, 105, 54, 49, 35, 137, -84, -44, -36, -89, 32, -59, -43, -61,
  -89, -76, 114, 98, 14, -6, -2, 0, -6, 14, 14, 66, 36, 65, 17, 66, -77, 53,
  -47, 58, -125, 80, -14, 44, 27, -59, 16, 11, -46, 94, 9, 14, -41, -55, -3,
  31, -79, -15, 0, -32, 73, 32, -62, -37, 45, 33, -81, -52, 7, 47, -8, -36,
  -6, 11, -15]

theorem fractionalNearFrameSubtreeG2R0101_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0101Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0101Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0101Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0101_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0101LowerBoundTable : List ℤ :=
  [-110, -5, -36, -138, -40, 1, 2, 2, 4, 9, 93, 69, -139, 241, -132, 168,
  256, 67, -117, 10, 15, 10, 89, 4, 115]

def fractionalNearFrameSubtreeG2R0101LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0101Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0101LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
