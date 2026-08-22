import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0091`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0091Mask : ℕ := 936556904424524

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0091Witness : Array ℤ :=
  #[-93, -179, -64, 67, -19, -180, -51, 64, -81, 285, 31, 5, 0, 155, 41,
  -58, -76, 45, -13, 88, 90, 83, 74, 146, -245, -174, -98, -215, -115, 66,
  101, 95, -75, 39, 9, 105, -205, -200, -116, 93, 41, 68, -34, -197, -25,
  13, 157, 171, 3, 45, 161, -78, -51, 34, -204, -86, 226, -10, -8, 138, 124,
  39, 244, -96, -60, -102, 68, 32, 172, 59, 43, 18, 40, 121, 64, -10, 0,
  199, 43, 42, -102, 26, -91, -43, -37, -45, 53, 48, -44, 0, 26, -155, -20,
  83, -167, 70, 128, 94, -1, -7, -18, 138, 17, 24, -117, -51, -60, -142,
  -10, 138, 1, -34, 76, 123, -17, -1, -89, -175, -10, -46, 76, -36, 60, -69,
  77, 50, -34, 37, -151, -71, 92, -5, -78, -101, -102, 117, 23, -3, 35, 35,
  48, 190, 36, 83, -153, 94, 56, -53, -93, -123, 207, 149, 91, -22, 78,
  -103, 239, 200, 116, 107, -35, -3, 8, 253, 107, 106, 56, 115]

theorem fractionalNearFrameSubtreeG1R0091_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0091Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0091Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0091Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0091_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0091LowerBoundTable : List ℤ :=
  [88, 380, 282, 2, 139, 197, 235, 1, 2, 9, -152, 237, 382, 79, 8, 10, 112,
  482, 402, 381, -8, 76, -512, 200, 824]

def fractionalNearFrameSubtreeG1R0091LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0091Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0091LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
