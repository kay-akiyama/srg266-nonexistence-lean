import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0257`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0257Mask : ℕ := 5356598077264980

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0257Witness : Array ℤ :=
  #[0, 28, 20, 70, 70, -145, -108, 16, 27, 45, 41, -32, -60, 16, 23, -12,
  -24, -6, 29, 72, 36, -47, -1, 24, 59, 5, -16, 3, 95, 16, 14, 41, -58, 4,
  90, 52, 0, 3, -31, 19, 65, 55, 17, -49, -34, -24, 3, 25, -23, 89, -2, 93,
  -86, -40, -21, 146, 48, 52, -61, 47, 40, 25, 74, 3, -65, 30, 48, 15, -39,
  36, 11, 31, -27, -27, 19, 37, 52, -8, -9, -34, 14, 18, 57, 9, 144, -14, 2,
  34, 37, -48, -19, -50, 23, 65, 59, 38, -36, -46, 9, -15, 57, -40, 0, 156,
  120, -86, 2, -9, 52, 135, 28, 114, -95, -78, -36, 52, -1, 30, 61, -35, 24,
  40, 7, -26, -85, 49, 18, 81, 10, 46, -43, 41, -58, 102, -33, 32, -69, -3,
  -1, -20, -4, -11, 36, -52, -114, 25, 35, 28, 73, 20, 6, -33, 32, -17, -46,
  -2, 22, 1, -11, -9, -30, 58, -54, 17, 42, -26, 0, 31]

theorem fractionalNearFrameSubtreeG2R0257_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0257Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0257Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0257Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0257_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0257LowerBoundTable : List ℤ :=
  [85, -6, 212, 259, 44, 187, 132, 63, 80, 200, 19, 80, 89, 156, 186, 10,
  138, 276, 400, 143, 240, 95, -39, 105, 142]

def fractionalNearFrameSubtreeG2R0257LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0257Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0257LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
