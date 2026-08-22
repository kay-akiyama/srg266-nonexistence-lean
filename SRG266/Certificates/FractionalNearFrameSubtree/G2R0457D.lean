import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0457`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0457Mask : ℕ := 5795149868599912

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0457Witness : Array ℤ :=
  #[24, 26, -19, 38, 12, 46, 16, 26, 21, -43, -37, -47, -25, -22, 17, -19,
  -74, -15, -31, 28, 10, 15, 9, 40, 20, -51, 84, -3, 22, 48, 35, 75, -59,
  -100, 26, 22, 25, -62, 0, -64, 61, 69, -39, 25, 11, 35, -33, -14, 60, -11,
  15, 26, 0, -32, -43, -40, 40, -26, -27, -12, 42, -45, 5, 52, 195, -31, 38,
  -6, 1, 31, 35, 7, 62, 23, -85, 2, 8, 20, -6, 10, 32, 7, 28, 66, -56, -43,
  -15, 29, 25, -35, -11, -21, 13, 8, -23, 30, 4, 32, -40, -12, 23, 8, -71,
  45, 30, -24, -28, -10, 0, -15, -15, 47, 19, 53, -77, -28, 6, -24, 23, -1,
  -34, -92, -29, 76, 30, -50, -9, -45, -28, 19, 18, -32, 31, -28, 10, -36,
  -24, -36, 15, 24, -14, -13, -8, -21, -6, -15, -44, 11, 44, 25, -76, 60,
  41, 5, -7, 45, 74, -55, 11, 4, 21, 37, 59, 5, 3, 14, 5, 41]

theorem fractionalNearFrameSubtreeG2R0457_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0457Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0457Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0457Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0457_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0457LowerBoundTable : List ℤ :=
  [-4, 1, 130, -94, 202, 1, 2, 136, -21, 13, 33, 10, -12, 73, 187, 91, 42,
  -36, -70, -64, -63, 126, 76, 65, 11]

def fractionalNearFrameSubtreeG2R0457LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0457Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0457LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
