import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0576`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0576Mask : ℕ := 6848690049192610

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0576Witness : Array ℤ :=
  #[16, 137, 60, -12, -28, -41, -39, 70, -49, -15, -35, 117, 79, 82, 40, 71,
  19, 82, 16, -23, -77, 10, 37, -75, -26, -38, 99, 67, 92, -51, -71, -72,
  -41, -30, 68, 34, 84, 116, 48, -76, 47, 4, 46, 31, 27, 5, 10, -53, 11, 45,
  -47, -10, -72, -95, 60, 7, 27, -3, -57, -12, 11, 54, -15, 117, 80, 47, -6,
  16, -36, 65, -3, -8, 92, -3, 36, 21, 12, -21, -62, 28, 19, 23, 72, -15,
  40, 35, -14, 24, -38, 35, 57, 62, -27, 1, 39, 37, -32, -20, -39, -1, -6,
  10, -2, 16, 26, -17, -57, 10, -57, -1, -32, -27, -79, 3, 23, 47, 33, 34,
  20, 9, -40, -108, -102, 22, 47, 36, 57, 4, -39, 101, 35, 102, -14, 93,
  -19, 149, 69, 58, 44, -1, 34, -44, 62, 25, 2, 40, -2, 62, -71, -17, 48,
  32, -101, 102, 7, -54, -35, -39, -14, 68, 5, -46, -31, -76, 0, -48, 130,
  48]

theorem fractionalNearFrameSubtreeG2R0576_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0576Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0576Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0576Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0576_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0576LowerBoundTable : List ℤ :=
  [56, 20, 170, 219, -18, 101, 271, 17, 218, 250, 289, 261, 108, -129, 162,
  100, 85, 18, 198, 142, 242, 109, 6, 412, 294]

def fractionalNearFrameSubtreeG2R0576LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0576Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0576LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
