import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0081`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0081Mask : ℕ := 2370130661848081

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0081Witness : Array ℤ :=
  #[22, 86, -10, 65, 0, 5, 1, -33, 0, 40, -119, -27, 73, 27, -65, 0, -61,
  -11, 24, 19, 3, -37, 6, 59, 34, 65, 45, -58, 30, 31, -37, 15, -9, 60, -48,
  1, 26, -18, 17, 45, 0, -68, -42, -100, -29, 13, 33, -26, 59, 15, -16, -84,
  -23, 31, -71, 40, 25, 37, 56, -26, 62, 10, -2, 22, -77, -36, -13, -16,
  -42, -5, 23, -2, -21, -21, 3, 20, 8, -7, 16, 29, -18, -7, 89, 9, -34, 63,
  -18, -42, 8, 51, -44, -60, 43, 2, 27, 67, 64, -23, -56, -40, -55, -89, 2,
  35, -17, -29, 48, -15, 0, 55, 66, -29, -17, -50, -48, -68, -30, -38, 4,
  110, -109, -122, -21, -17, 11, -6, 62, -16, -61, -17, -8, -30, 49, 67, 33,
  -45, -8, 51, 17, -46, -83, 68, 10, -34, -5, -46, 44, 45, 86, 51, 51, 10,
  9, 44, 125, -29, -4, -34, -25, -45, -48, 54, 35, -14, 23, 3, 106, 81]

theorem fractionalNearFrameSubtreeG3R0081_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0081Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0081Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0081Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0081_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0081LowerBoundTable : List ℤ :=
  [-50, 51, 7, 19, 3, 2, 95, -97, 51, 125, -6, 8, 11, 151, -22, -1, -244,
  -40, 113, 110, 224, -89, 189, 144, -32]

def fractionalNearFrameSubtreeG3R0081LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0081Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0081LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
