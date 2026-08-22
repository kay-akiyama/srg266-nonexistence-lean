import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0074`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0074Mask : ℕ := 962676795352152

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0074Witness : Array ℤ :=
  #[-32, 99, -150, 29, -31, 54, -13, 33, 41, -69, 29, -11, 90, 254, -17,
  225, 50, 84, 110, -22, 67, 4, 0, -130, -48, 31, -52, -152, -39, -108, -6,
  115, -50, 318, 238, -109, -221, -288, -208, 200, 275, 147, 167, 2, 131,
  165, -41, -98, -226, -130, -37, 76, -99, -271, -221, -86, -83, 34, 66, 28,
  0, 178, 32, 76, 170, 97, -10, 35, 29, -33, 102, -26, 76, -25, 42, 104, 92,
  -86, 120, -188, 288, -14, -179, -119, -73, -53, 96, 58, -168, 0, -17,
  -123, 72, 71, -104, -61, -5, 31, 32, 38, -22, 34, -12, -166, 142, 66, 30,
  -17, -2, -9, -125, -24, 0, 58, 9, 82, -16, -166, -112, 53, 46, 0, 61, 12,
  34, -15, 4, 64, -187, 224, -82, 200, -23, 65, -12, 54, 0, -201, 88, 60,
  -273, 106, 143, 118, 43, 189, -79, 407, 89, -58, 138, -37, -37, -5, -71,
  -71, 16, -39, 28, -3, 107, -40, 31, -241, -19, -35, -115, -5]

theorem fractionalNearFrameSubtreeG2R0074_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0074Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0074Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0074Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0074_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0074LowerBoundTable : List ℤ :=
  [-36, 156, -167, -10, -83, 210, 85, 34, 2, 608, 64, 358, -192, 204, 87,
  25, -341, 307, 382, 331, 9, 82, 192, 720, 269]

def fractionalNearFrameSubtreeG2R0074LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0074Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0074LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
