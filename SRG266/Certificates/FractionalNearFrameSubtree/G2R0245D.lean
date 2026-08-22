import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0245`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0245Mask : ℕ := 5161984514572632

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0245Witness : Array ℤ :=
  #[241, -43, 91, 10, -114, -122, -84, 307, 33, 11, 47, -185, 0, -41, 191,
  -56, 15, -24, -77, -107, 378, 221, -29, -45, 40, -75, 159, -147, 43, 128,
  76, 44, 80, 213, -244, -135, 214, -126, -313, -283, 54, -31, -140, -45,
  50, 0, 206, 158, -48, 26, -143, 147, 60, 152, -312, -60, 53, -17, 60,
  -280, -121, -32, 34, 139, 82, 86, 58, -142, -361, -135, -143, 86, 166,
  -171, 77, 331, 144, -323, 13, 1, -166, 127, -19, 67, 220, -148, -41, -414,
  -145, -172, 21, 174, 68, 15, 258, 178, -231, -75, 14, 141, 192, 323, 202,
  14, 38, 100, 41, 35, 144, 139, 334, 107, 66, -91, 86, -55, -39, -60, 259,
  -109, -74, 174, -137, 338, 475, 0, -466, -79, 106, -199, 164, 288, 163,
  -376, 24, 48, 409, -349, -191, 321, 218, 9, 41, -155, -91, -110, -131, 96,
  -82, -64, -8, -45, -208, -221, -360, 287, -206, 88, -94, -299, -36, -22,
  76, 57, 355, -165, -77, 133]

theorem fractionalNearFrameSubtreeG2R0245_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0245Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0245Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0245Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0245_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0245LowerBoundTable : List ℤ :=
  [-154, 60, 175, 1, 3, 1, 2, -138, 199, -93, 64, 9, 314, 1192, 609, 10, 9,
  -504, -118, -189, 839, 60, -322, 808, 670]

def fractionalNearFrameSubtreeG2R0245LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0245Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0245LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
