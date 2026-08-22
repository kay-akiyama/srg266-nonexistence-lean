import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0123`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0123Mask : ℕ := 5860178225728778

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0123Witness : Array ℤ :=
  #[23, -15, -31, -19, 19, -31, 19, -33, 62, 11, 5, 15, 17, -2, 4, -3, 4,
  -3, -5, -30, 0, 35, -19, 20, 29, -41, -10, 42, -4, -5, -16, 39, -14, -30,
  -19, -41, 57, 84, 54, -47, 69, 54, -57, -23, -43, 17, 6, -21, 43, 39, 42,
  -17, -6, -39, 4, -11, -28, -9, 7, 22, -4, 18, -6, 18, 33, -7, 0, -23, 14,
  55, 12, 15, 45, -3, 10, 10, -5, 26, -71, 5, 26, -6, -11, 10, 40, -38, -9,
  63, 44, -62, 68, 71, -17, -48, -60, 66, -51, 45, 20, -12, -3, 17, -23, -9,
  46, -31, 20, -33, 64, -66, 15, 48, 34, -71, 47, -68, 14, 25, -7, 43, 26,
  -13, -72, -38, -49, 65, -43, 15, 29, -47, 22, -23, 82, -46, 45, 47, 36,
  -8, -12, -3, 23, 16, -2, -6, -54, 32, 0, 37, -1, -73, -18, 56, -31, 45,
  -29, 4, -2, 40, -27, 9, 34, 31, -44, 29, -5, -11, 30, 12]

theorem fractionalNearFrameSubtreeG5R0123_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0123Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0123Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0123Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0123_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0123LowerBoundTable : List ℤ :=
  [-5, -21, 8, 64, 95, 43, 2, 78, 47, 267, 10, 104, 167, 7, 5, 44, 104, 44,
  103, 128, 66, 9, -68, 111, 43]

def fractionalNearFrameSubtreeG5R0123LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0123Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0123LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
