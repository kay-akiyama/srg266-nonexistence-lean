import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0166`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0166Mask : ℕ := 2368167398546449

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0166Witness : Array ℤ :=
  #[-51, -92, -143, -45, -184, 0, -46, 35, -43, -73, 0, -107, 234, 161, 216,
  129, 31, 134, 47, 83, 91, -20, 89, 21, 29, 67, 16, -42, -64, -105, -270,
  97, -13, -86, -114, -173, 4, 147, 99, 63, 109, -43, 12, -181, 216, -35,
  17, 46, -16, 74, 23, 34, -47, 18, 38, -154, -55, -80, 92, 98, 38, 99, 30,
  45, 10, 36, -11, 15, -57, 64, -5, -46, -37, -34, 14, 20, 19, -27, 6, -66,
  -45, 8, -2, 4, 33, 4, -44, -11, -7, -12, -87, 115, 36, 17, 40, -26, 11,
  -10, -70, -37, 18, 78, -16, -47, -19, -61, -54, -50, -40, -136, -22, -63,
  -61, -15, -17, -70, -27, -53, 29, 222, 43, 11, -88, 40, 65, -2, -109, 90,
  51, 6, 14, -3, 8, -9, -24, -5, -39, -76, -6, -10, 25, -2, 20, -2, -44,
  -19, -13, 76, -2, -15, 51, 23, 57, 60, -4, 130, -10, 67, -78, 16, 5, -36,
  -19, 43, 63, 15, 117, -115]

theorem fractionalNearFrameSubtreeG1R0166_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0166Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0166Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0166Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0166_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0166LowerBoundTable : List ℤ :=
  [-87, 127, -260, -55, -145, 2, 127, 245, 119, 195, 9, 55, 176, -114, -94,
  -212, 6, -17, -29, 215, 384, -243, 48, -131, 595]

def fractionalNearFrameSubtreeG1R0166LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0166Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0166LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
