import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0535`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0535Mask : ℕ := 6796591097434641

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0535Witness : Array ℤ :=
  #[18, 60, 16, -44, 0, 174, 0, 74, 73, 60, 34, 144, -85, 8, -44, -37, 14,
  -136, -11, -13, 0, -21, 13, 80, 40, -13, 9, -26, -13, 112, 10, 68, 7, 18,
  28, 13, 72, 76, -85, -73, 12, 16, 26, 83, -74, -61, 14, -2, 59, 39, -1,
  57, 16, -14, 19, 64, 1, 14, -23, 29, 36, 16, 21, 9, 76, -3, 35, 26, -67,
  9, 5, 26, -9, 36, -46, -59, 7, -18, 15, 51, 15, -47, -76, 84, 32, -31,
  -54, 20, 6, 7, 25, -12, 62, -36, 19, 7, 15, 8, -13, 10, 16, 44, 8, -130,
  -27, -120, -17, 45, 81, -120, -32, 57, -50, 9, 75, -54, 76, 97, -58, -124,
  179, 30, 57, 5, -27, 38, 89, 44, 10, 16, -16, 74, -13, 54, 35, -12, 36,
  -23, -1, -111, 32, 6, -62, -21, 51, 34, -24, 61, 72, 35, 50, -97, 1, -131,
  78, 28, 61, -124, 88, -65, 1, 57, -39, -138, -57, -88, 22, -25]

theorem fractionalNearFrameSubtreeG2R0535_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0535Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0535Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0535Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0535_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0535LowerBoundTable : List ℤ :=
  [47, 1, -58, 106, 126, 195, 40, 297, 59, 42, 14, 188, 116, 0, 88, 124, 14,
  10, -50, -81, 214, 18, 50, 93, 379]

def fractionalNearFrameSubtreeG2R0535LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0535Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0535LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
