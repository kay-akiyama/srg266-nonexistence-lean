import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0537`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0537Mask : ℕ := 6796865958556193

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0537Witness : Array ℤ :=
  #[109, 156, 98, 172, 165, 137, 112, 105, 116, 167, 232, 124, -309, -256,
  -256, -252, -275, -198, 27, -147, -53, -176, -53, 32, -126, -167, -37, -9,
  171, 177, 268, 267, 34, 40, 59, 57, 1, -39, -16, -14, 8, 6, -17, -72, 23,
  -2, 43, 12, 6, -26, -21, 39, -6, -56, 27, -11, -15, 18, -7, -26, -33, -9,
  -42, 41, -5, 18, -17, -33, 25, 64, 40, 17, -2, 7, 1, 13, -11, -11, -15,
  -39, 29, -48, 39, 35, 11, -29, -5, 29, 18, -22, -10, 18, 1, -12, -39, -11,
  -67, 22, 19, -25, 18, 24, -10, -5, -53, 0, -15, 61, 44, 56, 26, -17, 30,
  30, 24, 21, -90, -11, 37, 18, -64, -33, -5, 30, -37, -17, -11, -3, 7, -17,
  24, 27, -8, -11, 9, -10, 73, -21, -38, -12, 11, 5, 28, 19, 20, 13, 5, -29,
  37, 34, 18, 32, -13, 8, -7, 0, 7, -4, -7, 42, -4, 31, 16, 25, 8, -47, 39,
  29]

theorem fractionalNearFrameSubtreeG2R0537_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0537Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0537Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0537Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0537_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0537LowerBoundTable : List ℤ :=
  [35, 45, 1, -38, 108, 125, 126, 3, 125, 62, 14, 100, 66, 11, 12, 9, 97,
  -194, 9, 136, 20, 236, 242, 170, -211]

def fractionalNearFrameSubtreeG2R0537LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0537Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0537LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
