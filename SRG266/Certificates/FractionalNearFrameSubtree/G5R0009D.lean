import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0009`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0009Mask : ℕ := 806546090729545

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0009Witness : Array ℤ :=
  #[42, -4, -40, -144, 50, -15, -110, -77, -60, 5, -4, 74, -4, -6, 156, 63,
  122, -102, -73, -71, -65, 134, 103, -51, -42, -36, -21, 64, 0, 8, 82, 46,
  17, 13, 18, 42, 14, -7, 27, 29, -65, 48, -77, -66, 7, 21, -91, -28, -61,
  -28, 12, 22, 105, 67, 28, 49, 61, 81, -83, -20, 36, 26, 6, 45, -45, -11,
  -58, -15, 11, 57, 5, 3, 12, 63, 0, -48, -1, -2, 5, 18, -15, -3, -45, 26,
  64, 92, 94, 21, -20, -66, 24, -21, -17, 47, -44, 49, 26, -8, -16, -31, 5,
  8, 37, 65, -7, 33, 42, 26, -68, -29, -36, -63, 8, 8, -12, -58, -40, -39,
  -16, -86, 24, -92, 75, 82, -25, -2, 43, -15, -62, 67, -3, -105, 20, 38,
  36, 36, 11, -9, -41, 1, -28, 74, -66, 26, -111, 22, 75, 63, -31, -95, 24,
  12, 43, 49, 44, 32, -14, 22, -65, -76, 14, 43, 49, 74, -101, -87, 25, -45]

theorem fractionalNearFrameSubtreeG5R0009_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0009Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0009Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0009Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0009_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0009LowerBoundTable : List ℤ :=
  [-46, -47, 2, 77, 2, 75, 1, 14, 0, 9, 10, -91, 8, 247, 125, 87, -317, 37,
  166, 150, 203, -230, 162, 205, -25]

def fractionalNearFrameSubtreeG5R0009LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0009Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0009LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
