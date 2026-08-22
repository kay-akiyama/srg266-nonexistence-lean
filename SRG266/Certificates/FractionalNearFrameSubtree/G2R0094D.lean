import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0094`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0094Mask : ℕ := 1239990220458081

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0094Witness : Array ℤ :=
  #[173, 132, 136, 0, 63, -22, -117, -194, -10, -218, -132, -205, -20, 143,
  139, 0, 61, -31, -56, -5, -89, 39, -128, -10, 9, -118, -98, -206, 229,
  128, 135, 89, -57, -117, -207, -178, -299, 76, 257, 140, 216, 51, -105,
  -63, 0, 249, 193, -66, 0, -111, 52, -26, 39, 11, 102, 53, -42, 109, -46,
  57, 18, -118, 23, 105, 33, 29, 14, 108, 89, -27, -19, 69, -40, 85, 140,
  -2, -22, -35, -29, 14, 35, 72, 32, 7, 41, 103, 37, 107, 52, -4, 15, 24,
  -4, 10, 32, -55, 32, 68, 26, 118, 17, 91, -26, 139, 70, 34, 48, -3, 60,
  -30, 34, 45, 0, -61, 73, -29, -51, -118, 21, -35, 51, 101, -48, -64, -157,
  4, -14, 104, 16, -37, 93, -6, -35, 17, -34, 59, -60, 50, 55, 22, -62, 169,
  37, 1, 2, -13, -49, 61, -67, 36, -29, 51, 21, -33, 41, 41, -23, 73, 24,
  30, -20, -122, 115, -78, 56, 21, -78, 25]

theorem fractionalNearFrameSubtreeG2R0094_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0094Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0094Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0094Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0094_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0094LowerBoundTable : List ℤ :=
  [1, 1, 132, 165, 1, 61, 80, 389, 222, 8, 29, 40, 326, 160, 153, 8, 334,
  205, 281, 317, 299, 9, 242, 10, 379]

def fractionalNearFrameSubtreeG2R0094LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0094Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0094LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
