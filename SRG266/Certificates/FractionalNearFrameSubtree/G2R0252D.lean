import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0252`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0252Mask : ℕ := 5355636566638994

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0252Witness : Array ℤ :=
  #[93, 260, 129, -3, 13, 163, -9, 12, -71, 133, -93, -126, 6, 50, 0, -50,
  -19, 91, 34, 57, -170, -65, 41, 114, -16, 86, 83, 31, 170, 42, -9, -48,
  27, -49, 82, -35, 39, 4, 37, -16, 52, 59, 177, 30, 238, -75, 30, 35, -96,
  -127, 2, 6, 1, 46, -41, -1, 53, -177, 62, 58, 1, 172, -6, -81, -25, 0,
  -97, 106, -9, -3, 19, 50, -46, -51, -60, -6, -167, 52, 30, 52, 115, 57,
  -53, 1, 89, 8, 130, -52, 128, 204, 97, 49, 75, 91, 33, -44, -119, -37,
  -12, -84, -27, -117, 80, 12, -75, 47, 105, 116, 93, 63, -38, 6, 88, 10,
  -31, 52, 5, 101, 92, 34, 11, 93, -14, -125, 15, 39, -38, -37, 0, 60, -7,
  -9, 29, -67, 57, 13, 113, 12, -11, 17, 8, 50, -8, -81, -17, -65, -79, -49,
  6, -52, 18, 56, 33, -116, 66, 108, -238, 88, 1, -34, -54, -16, -60, 19,
  24, 74, -152, -52]

theorem fractionalNearFrameSubtreeG2R0252_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0252Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0252Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0252Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0252_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0252LowerBoundTable : List ℤ :=
  [73, -48, -7, 103, -9, 405, 1, 293, 275, 162, 9, 91, 333, 221, 108, 4,
  231, 268, 390, 375, 434, 78, 75, 126, 663]

def fractionalNearFrameSubtreeG2R0252LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0252Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0252LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
