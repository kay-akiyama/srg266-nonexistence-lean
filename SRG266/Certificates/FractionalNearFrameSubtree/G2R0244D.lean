import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0244`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0244Mask : ℕ := 5161973699889816

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0244Witness : Array ℤ :=
  #[41, -158, 207, 24, 59, 40, -26, 128, -117, -60, -96, -72, -84, 70, 74,
  161, -119, 72, -28, -44, -74, 5, -53, -76, -136, -100, 31, 148, 129, 124,
  216, -22, -152, -237, -12, 43, 58, -39, -24, -169, -24, -236, -25, -134,
  -65, -29, -53, 148, -38, 107, 50, 131, 166, 95, 177, 33, 169, 23, -145,
  -56, -38, -46, -99, -47, 218, -161, -10, -31, 20, 202, 138, -123, 164, 96,
  -13, -43, 151, 17, 69, -108, -49, 19, -32, -63, 54, 36, -14, -90, -5, 54,
  37, 0, -71, -153, 84, -98, -189, 39, -268, -21, -134, 14, 114, -156, 43,
  109, 20, -109, -11, 43, -5, 98, 76, -6, 24, -129, -73, 108, -22, -11, 9,
  -32, 0, 61, 132, -95, -203, 93, -33, -114, 16, 138, 45, 4, 0, 24, 128, -6,
  -158, 195, 147, 151, 66, 63, 97, -103, -95, 45, -106, -4, 116, -49, -23,
  105, 40, 100, 35, -21, -49, -41, 33, 217, -39, 12, -254, -210, -204, -21]

theorem fractionalNearFrameSubtreeG2R0244_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0244Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0244Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0244Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0244_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0244LowerBoundTable : List ℤ :=
  [-124, 2, -60, 162, -223, -361, -131, 80, 180, 10, 373, -91, 692, 250,
  -249, -125, 279, 9, -428, 9, 786, 237, -308, -319, 84]

def fractionalNearFrameSubtreeG2R0244LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0244Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0244LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
