import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0602`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0602Mask : ℕ := 6880972360893528

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0602Witness : Array ℤ :=
  #[43, 120, 75, -223, 0, -70, 86, -23, -65, -111, 124, 211, 21, -37, 7,
  110, 62, -25, 137, -43, 129, -41, 35, 23, -109, 43, -6, -90, 15, 44, -91,
  -159, 0, 58, 43, -16, 87, -78, -14, -40, 11, 47, 159, 149, 148, -122, 56,
  21, -76, -3, -73, -78, -74, -118, 100, 16, 65, -64, 52, -75, -82, 75, 64,
  -167, -78, -107, 24, -22, -74, -91, -57, 39, -18, 45, -52, -71, 6, -26,
  77, 222, 77, 180, 164, -108, -2, 38, -58, 142, -95, 57, -52, 104, 27, -35,
  -100, -30, 69, -100, 126, 82, 165, 10, 105, 44, 170, 0, 42, -8, 156, -37,
  141, 78, -8, -3, 42, 108, -44, -43, 216, -23, -60, 100, 72, -69, -20, 15,
  -46, -1, 100, 33, 6, -93, -41, -61, 12, 56, -9, 24, 23, 9, 176, -38, 235,
  103, 31, 119, 49, 206, 59, -21, 110, 0, -108, 78, 9, -67, -156, 0, -4,
  144, 1, 124, -14, -226, 156, 129, -75, 105]

theorem fractionalNearFrameSubtreeG2R0602_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0602Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0602Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0602Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0602_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0602LowerBoundTable : List ℤ :=
  [55, 464, 232, 48, 512, 146, 170, 1, 3, 92, 315, 410, 205, 812, 434, -54,
  -135, 632, 160, -110, 124, 438, 113, 102, 354]

def fractionalNearFrameSubtreeG2R0602LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0602Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0602LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
