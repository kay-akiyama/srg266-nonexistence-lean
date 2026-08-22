import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0084`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0084Mask : ℕ := 1041808359854320

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0084Witness : Array ℤ :=
  #[203, 227, 71, 76, 7, 161, 4, 23, 67, -113, -43, -124, -2, -150, 91, 116,
  79, 41, -93, 89, -4, 60, 25, -29, 39, 128, -2, -35, -108, -92, 1, 85, 76,
  6, 46, 48, 6, -88, 4, 125, -60, 15, -52, -28, 0, -21, 197, 36, 109, -61,
  -25, 1, 46, -112, -61, -26, 37, -26, -24, 45, 3, 50, 13, 6, 82, -97, -8,
  103, 78, 44, 10, 24, 27, 37, 0, 7, 89, 141, 93, -18, -29, 115, 94, 36, 57,
  41, -20, 64, 23, 13, 76, 84, -121, -9, 106, -4, 160, -6, 30, 14, 9, 26,
  114, 94, -47, 111, 14, 6, 12, -24, -20, -49, -104, -11, -24, 2, 4, 43,
  -162, -20, 94, -8, -47, -100, 76, 10, -19, 31, 11, 28, 73, -52, 104, 23,
  -67, 47, -93, -54, -134, -45, 0, -111, -108, 1, 80, -101, 107, 111, 27, 8,
  55, -5, 41, -2, 130, 45, -106, -71, 21, 75, 25, -82, 70, -54, 94, 43, -40,
  127]

theorem fractionalNearFrameSubtreeG2R0084_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0084Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0084Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0084Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0084_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0084LowerBoundTable : List ℤ :=
  [79, 33, 114, 172, 139, 83, 315, 170, 196, 9, 50, 169, -235, 328, 434,
  -45, 304, 336, 69, 197, 361, 566, 817, 532, 380]

def fractionalNearFrameSubtreeG2R0084LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0084Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0084LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
