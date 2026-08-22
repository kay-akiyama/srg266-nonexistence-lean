import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0106`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0106Mask : ℕ := 960513384849740

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0106Witness : Array ℤ :=
  #[70, -45, -59, -82, 28, -77, -34, -13, 76, -64, 23, -22, 153, 230, 19,
  51, -65, -130, -74, 98, 35, 45, 71, 85, -17, 58, -52, 137, -119, -28, 105,
  -6, -119, 99, -89, 36, 82, -12, 124, -24, 99, -36, 79, -64, -39, -20, -8,
  -16, -43, 63, 30, 43, 144, 8, 131, -75, 77, 0, 53, 9, -45, -16, 40, 67, 6,
  88, -12, 44, 36, 106, -32, 47, -18, 62, 96, 97, -48, 46, 7, -41, 11, 107,
  -4, 194, -15, 119, 75, -19, 1, -46, 131, 23, 97, 121, -80, -24, 107, 109,
  -35, 91, -83, 111, 53, 80, 197, 85, 48, 65, 127, 123, -66, -113, 11, 24,
  8, 33, 70, 101, 50, 11, -45, 42, 43, -40, -99, 87, -87, 11, 86, 64, 136,
  61, -137, -10, -48, -45, 32, -144, 43, 88, -117, -76, -69, -87, 14, -41,
  -88, 96, -21, 58, -11, -76, -138, 84, -2, 107, -66, -27, 21, -8, 43, 107,
  -141, 88, -88, -41, -151, 21]

theorem fractionalNearFrameSubtreeG1R0106_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0106Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0106Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0106Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0106_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0106LowerBoundTable : List ℤ :=
  [114, -134, 381, 208, 248, 416, 113, 166, 2, 352, -120, 101, 58, 775, 376,
  350, 10, 300, 633, 283, 256, 477, 10, 54, 119]

def fractionalNearFrameSubtreeG1R0106LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0106Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0106LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
