import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0438`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0438Mask : ℕ := 5786285077336660

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0438Witness : Array ℤ :=
  #[3, 76, 53, 36, -1, 5, 87, 84, -60, -60, 137, -122, 4, -48, -91, 61, -43,
  -32, -16, -34, -63, -77, 48, 15, -38, 107, 57, 134, 62, 103, 19, -37, -14,
  -87, 61, 206, -4, -88, 158, 29, 0, -29, 39, 17, 21, 176, 158, 72, -48, 12,
  -92, -143, -91, 24, -41, 63, 6, -56, -35, 43, 66, 116, -38, 64, -63, 122,
  92, 14, -119, 111, -28, -74, 205, 17, 144, 88, -65, -103, -72, -15, 86,
  -129, 5, 55, -1, -48, 154, 37, -125, -4, -28, -53, 30, -10, 61, 104, 17,
  -68, 103, -64, 48, 35, 55, 94, -16, 77, 111, -37, -161, 49, 79, 107, 107,
  33, 116, 70, 16, -3, 58, 161, 102, -75, -151, 112, 96, -24, 13, 34, 31,
  50, 178, -23, 28, 114, 147, 31, -1, 173, -3, 137, 107, 96, 95, 66, 42, 49,
  -79, 121, -201, 71, -113, -169, 103, -192, -26, 95, 73, -10, -41, -49,
  -71, -28, -22, 65, 110, -4, 26, -16]

theorem fractionalNearFrameSubtreeG2R0438_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0438Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0438Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0438Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0438_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0438LowerBoundTable : List ℤ :=
  [205, 228, 243, 145, 333, 151, 3, 93, 388, 539, 203, 336, 655, 525, 11,
  -5, 689, 247, 240, -200, 426, 270, 674, 77, 293]

def fractionalNearFrameSubtreeG2R0438LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0438Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0438LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
