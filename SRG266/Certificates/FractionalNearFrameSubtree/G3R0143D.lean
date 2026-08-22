import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0143`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0143Mask : ℕ := 6848287392501258

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0143Witness : Array ℤ :=
  #[-12, -23, -35, -17, -69, 111, 63, 18, 112, 145, 49, -235, -125, -169,
  -139, 64, -13, 5, -111, -93, 39, -124, -78, -175, -21, -78, 61, 33, 3, 14,
  65, 4, -70, 152, 68, 116, 124, -17, 130, 80, 57, 45, 101, -2, 45, 195, 17,
  -27, -17, -54, 100, 29, 103, -119, 19, 122, -398, -61, 106, -45, -7, 23,
  -29, 185, 36, 8, -322, -5, -48, -89, 211, -57, 57, -74, -89, -132, 174,
  27, 42, 87, 113, 105, 66, 18, 160, -45, 125, -20, -131, 54, 23, 96, -38,
  0, -75, 271, 30, -32, -11, -81, 77, -77, -77, 70, 29, 97, 138, 116, 409,
  316, -167, -168, -64, -219, 11, 41, -74, -50, -14, 254, 121, -16, -131,
  -222, -14, -27, 39, 60, -64, -112, 30, -7, 105, 53, 179, 45, 46, 0, -7,
  -17, -45, 8, 6, -115, -97, 110, 102, -3, -24, 98, 171, -60, 115, 66, 50,
  -30, 33, 104, 106, 94, -9, -205, -44, -85, -198, -120, 85, 116]

theorem fractionalNearFrameSubtreeG3R0143_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0143Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0143Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0143Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0143_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0143LowerBoundTable : List ℤ :=
  [-21, 169, 246, 183, 1, -57, 371, -68, 2, -189, 618, 464, 447, 9, 466,
  251, 156, -142, 213, 10, 205, 6, 557, 10, -447]

def fractionalNearFrameSubtreeG3R0143LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0143Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0143LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
