import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0402`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0402Mask : ℕ := 5741403383738792

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0402Witness : Array ℤ :=
  #[69, -60, -86, -166, 8, -7, 3, -216, -43, 34, 263, 108, 31, 50, 9, 9,
  -74, 107, -14, 95, 100, -88, 188, 18, -36, -213, -37, -78, 139, 75, 71,
  -144, -117, 109, 136, -221, -95, -134, 63, 138, 51, -7, 4, -60, 53, 13,
  -76, -26, -138, 4, 53, -123, 162, -40, -52, -40, -123, 6, -40, 65, -117,
  30, 32, -55, -51, 251, 3, 14, 60, -127, 301, 132, -221, -101, 52, -190,
  59, 52, -143, -23, 135, 43, 39, 11, 145, -43, 36, 80, 12, 68, 12, 26, 86,
  59, -44, -35, 143, 59, 132, 80, 90, -24, 71, -12, -166, -68, -7, -45, -70,
  24, -158, 49, -57, 9, 102, -165, -4, 46, 173, -97, 63, -30, -287, -256,
  180, 52, -29, 149, 118, 77, 193, -22, 109, -6, 271, -229, 2, 8, 17, 150,
  88, -123, 100, 64, 148, 105, 43, 79, 27, -77, 87, 103, 45, -201, 57, -52,
  75, -39, -73, -36, -26, -9, 52, -144, 121, 79, -15, -9]

theorem fractionalNearFrameSubtreeG2R0402_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0402Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0402Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0402Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0402_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0402LowerBoundTable : List ℤ :=
  [-37, 159, -30, 50, 152, 43, 315, -1, -11, 516, 1199, -206, -382, 9, 333,
  9, -97, 245, 158, -293, -110, 360, 128, 471, 69]

def fractionalNearFrameSubtreeG2R0402LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0402Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0402LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
