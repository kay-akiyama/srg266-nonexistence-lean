import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0001`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0001Mask : ℕ := 244965208346769

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0001Witness : Array ℤ :=
  #[38, 2, 32, 129, -15, 136, 65, 30, -92, -94, -204, 10, 0, 36, 103, -60,
  -16, -106, -9, -7, -143, -95, -61, 91, 45, -70, 13, -79, 164, 262, 66,
  -18, 81, 46, -30, 114, 39, -36, -3, 4, 45, 81, -156, 23, 121, 47, 59, -85,
  18, 100, 129, -120, -63, -75, -109, 219, -70, -174, -27, 62, -17, 150, 42,
  21, 110, -5, 85, -33, 24, 41, 50, -151, 120, 97, -9, 174, -136, 83, 32,
  276, 7, 142, 62, -10, -159, -44, 50, 13, 11, 29, 68, -21, -60, 70, 186,
  -26, -7, 92, -5, -38, 100, 8, -149, 74, -286, 55, 78, -185, -54, 242, 69,
  27, 88, 64, 42, 24, 207, -60, -62, -79, -82, 185, 3, -123, 45, -85, 101,
  39, 59, -113, -51, 3, 50, -55, 156, -77, -21, 8, 99, -59, 160, 94, 1, -43,
  69, -22, 17, 5, 20, 60, -116, 87, -273, -14, -76, 76, 84, 158, 38, 82, 52,
  -81, 65, 6, 200, 206, -286, 179]

theorem fractionalNearFrameSubtreeG2R0001_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0001Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0001Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0001Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0001_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0001LowerBoundTable : List ℤ :=
  [66, 241, 155, 57, 1, 2, 247, 79, 382, 44, 280, 466, 284, 67, 336, 196,
  296, 301, 699, 75, 823, 377, 218, 271, 10]

def fractionalNearFrameSubtreeG2R0001LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0001Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0001LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
