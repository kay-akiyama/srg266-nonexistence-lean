import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0061`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0061Mask : ℕ := 969067722146890

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0061Witness : Array ℤ :=
  #[65, 26, -99, 15, 7, 70, -60, -33, -60, 56, -30, -18, -39, -28, 0, 27,
  68, 1, -40, 10, 35, -49, -40, 20, 0, -31, 58, 21, 0, 16, -1, -95, -65,
  -76, -52, 51, 5, 75, 19, 52, 25, 60, 4, -8, -19, 25, -70, -23, -3, 7, 33,
  14, 6, 12, 43, -50, 25, 39, -11, -27, -16, 7, -14, 42, -4, -16, -16, -8,
  117, 32, 24, 70, 82, 31, 49, 34, -11, 29, -6, 67, -43, 18, 23, 17, -33,
  22, 8, 24, -10, 19, 67, 57, -18, 10, 33, -9, 17, -12, 59, 8, -8, -27, -32,
  22, -7, -21, -35, 17, -18, 34, 10, 17, 13, 0, 8, 27, 69, -18, -15, -10,
  -4, 20, -19, 19, 15, 1, 9, -24, 29, -44, -38, 2, 73, -75, 3, 40, -35, -69,
  42, 22, -19, -9, -38, -46, -79, 6, -50, 13, 5, -36, -33, 3, -1, -17, 61,
  53, 35, 18, 3, 47, -2, 17, 59, 11, 1, 40, -12, 7]

theorem fractionalNearFrameSubtreeG3R0061_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0061Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0061Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0061Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0061_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0061LowerBoundTable : List ℤ :=
  [2, 2, 70, 106, 85, 86, 2, 63, -51, 97, 67, -49, 54, 228, 112, 178, 86,
  205, 287, -44, -176, 9, 62, 155, 85]

def fractionalNearFrameSubtreeG3R0061LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0061Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0061LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
