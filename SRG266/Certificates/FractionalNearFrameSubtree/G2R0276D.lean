import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0276`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0276Mask : ℕ := 5372456396767820

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0276Witness : Array ℤ :=
  #[61, 39, 25, 66, 94, -14, -9, -23, -17, -19, 14, -74, -5, -26, 1, -69,
  75, 19, 8, 12, -20, -16, 22, -51, -26, -55, 111, 55, 0, 33, -14, -12, 114,
  41, 7, 10, 0, 6, -16, -112, -46, 9, -54, 10, 42, 9, 61, -40, -4, 37, 5, 3,
  -36, -30, 23, 23, -39, -34, -4, 20, 17, 18, -25, -35, -3, 64, 21, -24, 6,
  -70, 39, 45, 13, 26, 12, 49, 61, -20, -26, 38, 18, -75, -18, -7, 10, -8,
  -58, 26, -64, -63, 53, -8, -51, -15, 6, -15, 22, -10, 60, 17, 17, 30, 1,
  -48, 20, 6, -13, 43, 75, 37, 6, -26, -2, 28, 81, -12, 30, 49, 46, -79,
  -64, 6, 15, 35, 21, -8, 5, 51, -6, 61, 70, -8, -16, -6, -33, 27, 28, -3,
  -10, 25, -15, 62, 7, -63, 24, -40, 67, 41, 14, 14, -10, 16, -10, 16, -55,
  -86, -31, -81, 68, -95, 79, 47, -51, -37, -2, 15, 18, -30]

theorem fractionalNearFrameSubtreeG2R0276_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0276Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0276Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0276Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0276_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0276LowerBoundTable : List ℤ :=
  [2, 1, -39, 2, 29, 126, 100, 59, 60, -10, 216, 18, 247, 12, 119, -106,
  -24, 10, -130, -39, -1, 20, 162, 57, 374]

def fractionalNearFrameSubtreeG2R0276LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0276Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0276LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
