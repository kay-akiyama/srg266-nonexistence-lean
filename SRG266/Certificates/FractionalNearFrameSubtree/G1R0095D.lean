import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0095`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0095Mask : ℕ := 944248035257496

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0095Witness : Array ℤ :=
  #[183, 179, 141, 164, 64, 51, 42, -145, -103, -96, -20, -112, -42, -150,
  -21, -71, -82, -45, -221, 73, 54, -8, 30, -62, 44, 90, 124, 86, 63, 9,
  110, -57, -148, 42, 158, 57, 29, -97, 35, -49, 15, -6, 17, 122, 17, 171,
  36, -134, -118, -112, 76, 169, 67, -145, 39, 64, -78, -41, 32, 103, 85,
  40, 14, -25, -11, 32, 82, -44, -65, -91, 0, 43, -70, -20, -63, 39, 77,
  156, 145, -6, -44, 64, -25, -52, -46, 83, 56, 99, 42, 29, 30, 18, 63, -36,
  -7, 49, -63, 82, -112, 10, 19, -91, -16, 60, -109, -17, -102, -69, -61,
  -5, -74, 107, -55, -15, 0, 57, -94, -93, -87, -119, -87, -132, 98, 84, -1,
  -82, 81, 23, -87, 5, 19, -26, -4, -24, -138, -57, -47, 6, 65, 70, -15, 50,
  -7, -6, 26, -40, 48, 74, 35, -9, 58, 10, -6, -21, 106, 97, -95, -53, 52,
  47, -43, -10, -73, -23, 11, -43, -6, 110]

theorem fractionalNearFrameSubtreeG1R0095_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0095Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0095Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0095Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0095_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0095LowerBoundTable : List ℤ :=
  [-113, -60, 20, -40, 88, 48, 47, 47, 2, -7, 31, -39, -272, 261, 258, -19,
  111, 306, 38, 193, -50, -45, 9, 433, 169]

def fractionalNearFrameSubtreeG1R0095LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0095Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0095LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
