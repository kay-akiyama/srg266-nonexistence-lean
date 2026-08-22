import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0123`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0123Mask : ℕ := 969526677201320

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0123Witness : Array ℤ :=
  #[4, -8, -19, -67, 40, 16, 49, 0, -19, 54, -27, 185, -25, -36, 20, 79, -7,
  25, -149, 35, 41, -10, -57, 39, -1, 16, -52, -8, 139, 38, 156, -90, 24,
  -46, 57, -90, 89, -43, -95, 2, 2, -12, 1, 14, 18, 140, -40, 90, -24, 47,
  13, 36, 68, -56, -81, 21, 82, -59, 99, 5, -48, 7, 2, 51, -11, 38, -77, 73,
  38, 4, 54, -23, 50, -25, 3, -52, 99, -83, -51, -88, -10, 40, 66, -37, 18,
  -52, -53, -165, 99, 61, 97, 32, 49, -60, 213, -42, -15, -53, -43, -86,
  -43, -49, 29, -20, -19, -2, 64, 39, 47, -47, -119, -52, -4, 0, 35, 18, 75,
  -15, 18, 17, -47, -24, 40, -7, 47, 11, -77, 14, -116, 48, -22, 39, 36, 50,
  49, 83, -1, -81, -11, -29, -32, -34, -50, -6, 12, -72, 13, 12, -19, -30,
  63, -7, 76, -21, 45, -38, 53, -12, -14, 26, -6, 10, -3, 80, 4, 24, 54,
  -61]

theorem fractionalNearFrameSubtreeG1R0123_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0123Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0123Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0123Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0123_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0123LowerBoundTable : List ℤ :=
  [-25, 19, 194, -86, 1, 120, 163, 1, 72, 108, 97, -54, 10, 11, 11, 21, 353,
  -124, 26, 68, 9, 272, -25, 84, 25]

def fractionalNearFrameSubtreeG1R0123LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0123Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0123LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
