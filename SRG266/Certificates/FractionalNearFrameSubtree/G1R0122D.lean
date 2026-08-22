import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0122`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0122Mask : ℕ := 969522921316712

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0122Witness : Array ℤ :=
  #[141, 134, 76, -114, -97, -41, -5, 17, 92, 62, -24, -104, 58, -33, 106,
  -41, 83, -33, 51, -55, -22, -109, -97, -3, -7, 41, 42, 18, 55, 98, 8, -30,
  -78, -43, -9, 156, -121, -115, 51, -93, 105, -27, 75, 65, -99, -114, -48,
  -12, -39, -29, -58, 49, 93, 155, 69, 67, 24, 12, -59, 18, 49, 93, 13, -66,
  28, -7, -38, 24, 17, 100, -33, -47, -9, 21, -55, 99, 105, 7, -10, 42, -61,
  -13, -191, -60, 24, 65, 12, -118, 61, -67, -9, 76, 86, 114, -50, 16, -97,
  83, 60, 12, 77, 13, 69, -16, 190, -28, 73, 0, -39, -4, -85, 106, 8, -51,
  48, -3, 27, -45, 8, -123, 53, 34, 9, 12, 44, 126, -41, -81, 102, 104,
  -102, -131, 142, 53, 35, 46, 56, -20, -110, -41, -5, 33, -43, -55, -91,
  37, -44, 60, -107, 83, -77, 1, -54, -59, -61, 103, -42, 144, -5, 41, -27,
  39, 174, 21, 131, -14, -50, 24]

theorem fractionalNearFrameSubtreeG1R0122_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0122Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0122Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0122Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0122_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0122LowerBoundTable : List ℤ :=
  [-52, 2, 146, 35, 48, 122, 129, 2, 150, 6, -46, 319, 140, 490, 434, 191,
  -60, 166, -108, 298, 224, -223, -155, 224, 203]

def fractionalNearFrameSubtreeG1R0122LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0122Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0122LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
