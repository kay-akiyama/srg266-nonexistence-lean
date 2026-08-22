import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0162`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0162Mask : ℕ := 1871114944285040

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0162Witness : Array ℤ :=
  #[-21, 143, 74, 123, 123, 14, 4, -14, 17, 39, -135, -90, -159, 36, -85, 4,
  -51, -43, 38, 85, -5, -10, 40, -35, -19, 134, 82, -21, 18, -36, -20, 10,
  29, 15, 55, 120, 59, -34, -78, 103, -92, 28, 65, 42, 12, 102, 8, -22, -24,
  -4, -36, -67, -151, -123, 124, 48, -3, 35, 17, 1, 24, -8, 2, -94, -27,
  123, 2, 37, 108, -33, -32, 47, -66, -95, 119, 51, -106, 140, 114, -57,
  -21, -1, -4, 56, -165, -69, -52, 51, 3, -15, -8, -61, -88, -46, 26, -84,
  -29, 40, -23, -55, -90, -17, 13, 138, -20, 31, 63, -83, -1, -46, -13, -27,
  -51, 36, -47, 4, -31, 0, 17, 91, 26, -101, 85, -23, -14, -20, 59, 68,
  -113, 16, -67, -61, 57, -30, 66, 71, 10, 50, -35, -71, 7, -44, -37, 100,
  58, 0, 114, 41, -33, -60, 31, 122, 37, 8, 156, 25, 32, 27, -54, 49, -91,
  -104, 29, -74, 6, 129, 84, 153]

theorem fractionalNearFrameSubtreeG1R0162_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0162Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0162Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0162Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0162_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0162LowerBoundTable : List ℤ :=
  [-31, 126, 25, 120, 118, 56, 2, 27, 2, 399, 45, 52, -95, -130, 77, -300,
  129, 328, 10, -250, 63, 8, 454, 667, -98]

def fractionalNearFrameSubtreeG1R0162LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0162Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0162LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
