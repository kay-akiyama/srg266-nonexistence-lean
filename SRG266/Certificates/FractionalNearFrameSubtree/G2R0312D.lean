import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0312`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0312Mask : ℕ := 5388932965057100

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0312Witness : Array ℤ :=
  #[-16, 96, -8, 82, 108, 89, -60, 36, 94, -2, 62, -151, -42, -84, -161,
  -31, 44, 20, 8, -43, -11, 6, -10, 29, 5, 2, 192, 36, 0, 30, 29, -25, 75,
  32, -30, -23, 86, 31, 17, -86, -84, -41, 11, 129, 22, 54, 33, 20, -36,
  -33, -5, 19, 27, 21, -30, -34, -28, -24, 90, 12, -11, 73, 19, 5, -26, 0,
  64, -34, 5, 10, 20, 14, 78, 18, -42, -3, -10, 22, 5, -2, 32, 49, 48, -16,
  48, 80, 13, 68, 86, -35, -33, -40, 33, -61, 5, -29, 60, 66, 19, 7, -39,
  -15, 67, 8, 73, -2, 3, -9, -12, 7, 26, 44, -34, -9, -45, -5, -5, -79, 11,
  27, 29, -47, 35, 40, -7, 13, 7, -3, -137, 63, -37, -15, 16, -18, -57, -23,
  0, 33, -66, 3, 54, 65, 44, 11, -79, 102, 59, -9, -30, 49, -18, 18, 40, 99,
  21, 10, -26, -39, 45, -63, -25, -1, 55, 104, 34, 2, 37, -11]

theorem fractionalNearFrameSubtreeG2R0312_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0312Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0312Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0312Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0312_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0312LowerBoundTable : List ℤ :=
  [64, 70, 146, 43, 115, 160, 1, 11, 133, 1, 165, 83, 54, 81, 186, 142, 272,
  219, 156, 11, 185, 180, 202, 181, 488]

def fractionalNearFrameSubtreeG2R0312LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0312Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0312LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
