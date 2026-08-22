import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0020`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0020Mask : ℕ := 690045286863369

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0020Witness : Array ℤ :=
  #[210, 194, 106, 147, 230, 148, 81, 13, -134, -219, -15, 0, -113, -54,
  -89, -124, -206, -180, -62, -45, -34, 3, -34, 50, 51, 14, -146, -104, 84,
  104, 247, 46, 24, 12, -90, 194, 49, 100, 142, 43, -94, -52, -43, -144, 43,
  21, 107, 7, 36, -55, 19, -76, -136, 110, 68, 26, -40, -50, -24, -38, -23,
  65, -26, 54, 117, 44, -124, -57, -19, 54, 112, 22, 2, 35, -92, 24, 35,
  -55, 68, -27, 63, -45, -89, -38, -69, -38, 5, 22, -11, -28, -88, -220, 31,
  -40, -77, -103, -31, -98, -12, -5, 75, 17, 21, 123, -120, -83, -142, -3,
  72, 115, 34, 0, -29, -53, 6, -70, 141, 53, -19, 56, 6, 13, -53, 26, 39,
  53, 67, 18, 5, 43, 85, -21, 94, 66, 113, -115, 63, 8, 32, -13, 97, 108,
  194, 19, 80, 17, 69, 113, -4, -25, 58, 27, -53, -164, -170, 113, 53, 38,
  -102, 68, -30, 22, 7, -50, 93, 65, -3, 29]

theorem fractionalNearFrameSubtreeG2R0020_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0020Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0020Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0020Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0020_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0020LowerBoundTable : List ℤ :=
  [-40, 277, -115, -81, -83, 98, 1, 139, 253, 213, 139, 159, 324, -36, 169,
  132, 171, 101, -201, 327, 70, 200, -6, 100, 181]

def fractionalNearFrameSubtreeG2R0020LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0020Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0020LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
