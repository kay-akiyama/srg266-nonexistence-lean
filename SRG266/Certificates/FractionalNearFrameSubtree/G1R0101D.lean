import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0101`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0101Mask : ℕ := 954122465315156

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0101Witness : Array ℤ :=
  #[203, -11, -171, -207, -261, 226, 132, 151, 158, 257, -121, -68, -178,
  -31, -17, -107, -1, -5, -185, 52, -6, -5, -44, 161, 72, -8, -32, 44, 155,
  -223, -232, -196, 207, 241, -134, -214, 102, 248, 393, -209, -286, -212,
  -94, 114, -93, 2, 28, 72, 7, -57, -11, 164, 40, -90, -198, -153, -244,
  205, 226, -25, -49, 30, 125, -148, -131, 112, -9, -3, -3, 33, -9, -53,
  -21, -30, -36, -149, -64, 144, -45, 94, 84, 187, -44, 111, -86, 197, -87,
  44, 99, 68, 85, 114, 182, 80, 87, 150, 103, 191, -19, 132, 45, 155, 26,
  138, -104, 127, 83, 8, -64, -39, -23, -88, 95, 271, -120, -164, -7, -53,
  -107, 4, -73, 78, 94, 117, 169, -51, -132, -288, 210, -111, 36, -40, -82,
  -208, 150, 79, 30, 136, -22, 56, 46, 26, -174, 93, 52, 54, -192, -36, 34,
  -13, 26, -70, -37, 95, -154, -33, 74, 58, 144, 159, 23, 35, -4, 83, -93,
  -32, 10, 66]

theorem fractionalNearFrameSubtreeG1R0101_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0101Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0101Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0101Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0101_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0101LowerBoundTable : List ℤ :=
  [-56, 3, 76, 365, 190, 2, 74, 139, 2, -217, -27, 10, 259, 374, -143, 109,
  -483, 583, 243, 395, 218, 664, 249, 163, 140]

def fractionalNearFrameSubtreeG1R0101LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0101Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0101LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
