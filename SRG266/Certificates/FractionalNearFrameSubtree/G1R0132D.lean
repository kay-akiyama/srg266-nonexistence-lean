import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0132`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0132Mask : ℕ := 1022233675416326

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0132Witness : Array ℤ :=
  #[21, 6, 3, -67, 27, -115, 170, 181, 90, 3, 96, 168, -205, -61, -31, -178,
  -131, -70, -13, 26, -46, -4, -68, 13, -17, -91, -48, -7, 24, 38, 48, -7,
  43, -24, -65, 8, 3, -1, 102, 33, 47, 2, -55, 60, 34, 6, 23, 37, 22, -39,
  38, 37, 14, -46, -103, -119, 60, 14, 55, -7, -28, 33, -74, 60, -76, -48,
  56, -47, -11, 100, 33, -17, 20, 31, -10, 94, 58, -2, 21, -5, 21, 44, -8,
  -69, 19, 5, -19, 40, 14, 6, 80, 45, -8, 83, -108, -11, 72, 0, 94, 51, 109,
  50, 59, 48, -22, 81, -36, -23, -17, -17, 22, -50, -9, -3, -13, -71, -55,
  -79, -136, 35, 6, -117, 52, -20, -95, 6, -51, 41, 20, 94, 1, 66, 55, 94,
  28, 38, -67, 43, 42, -9, 24, 81, -41, 132, -38, 10, 5, 7, 39, -98, 11, 10,
  165, -22, 117, 9, 39, -17, 9, 29, -29, 119, 2, 194, 62, 99, 0, 64]

theorem fractionalNearFrameSubtreeG1R0132_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0132Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0132Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0132Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0132_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0132LowerBoundTable : List ℤ :=
  [43, 270, 254, 109, -87, 200, 2, 114, 3, 113, 285, 218, 129, 104, 178, 3,
  10, 291, -116, 285, 65, 138, 10, 178, 272]

def fractionalNearFrameSubtreeG1R0132LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0132Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0132LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
