import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0513`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0513Mask : ℕ := 5812277926618388

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0513Witness : Array ℤ :=
  #[-80, 38, -35, -64, -19, -3, 112, 41, 18, 85, -27, -21, 20, 57, 0, 135,
  -49, 24, -137, 16, -27, 30, -20, -83, 78, 99, 73, 23, -72, 99, -63, -55,
  -65, -28, 12, 160, 149, 136, -68, -41, 29, 62, 118, 40, 123, -12, 0, 82,
  58, -90, -17, -86, 146, 62, 66, -91, -3, 18, -42, -111, -21, 12, -9, 74,
  41, 83, -23, -47, -14, -26, -97, 67, 63, 63, 80, 30, 24, 66, 5, 87, 3,
  -36, -26, -28, 14, 96, 80, 9, -68, 27, -46, -15, 43, 102, 26, 17, 16, -9,
  60, -43, 59, 146, 30, 14, 32, -22, 1, -111, 98, 9, 119, -77, -44, 52, 32,
  91, 51, 108, -39, 154, -12, 38, 169, 8, -84, -47, -10, -73, -13, -97, 28,
  128, 103, 13, 33, 17, -71, -125, 138, -145, -125, -40, 81, -75, -95, -72,
  -91, 50, -26, -38, 59, 20, 113, 45, -79, -60, -26, 54, 85, -162, 42, -49,
  30, -136, -90, -29, -22, -93]

theorem fractionalNearFrameSubtreeG2R0513_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0513Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0513Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0513Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0513_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0513LowerBoundTable : List ℤ :=
  [-2, -167, 2, 13, 110, 197, 136, 273, 10, 290, 59, -37, 312, 77, 445, 169,
  105, 167, 109, 46, 7, 189, 243, 85, 590]

def fractionalNearFrameSubtreeG2R0513LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0513Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0513LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
