import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0323`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0323Mask : ℕ := 5390512409905520

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0323Witness : Array ℤ :=
  #[162, 118, 115, 80, 108, 27, -98, 47, -176, -371, 63, -50, -31, -83, 48,
  -77, 0, -158, 75, -79, 61, 35, 203, -74, -9, -28, 62, 2, -74, 91, 116, 19,
  -129, 49, -111, 32, -60, -27, 44, 73, -94, 0, 72, 122, 1, -156, -74, -92,
  -36, -76, -31, -27, -9, 9, -147, 90, 195, 60, 0, 21, 86, -17, -9, 28, 46,
  -83, -92, 241, -67, -60, 211, 0, -59, 89, 118, 45, 148, -50, 113, 174,
  -68, -48, 77, 5, -25, -47, 47, -9, 84, -83, 20, -17, 15, -5, 108, -180,
  -8, -43, 90, 31, 94, 4, 83, 10, 0, 92, 180, -104, 45, 27, -207, -143,
  -112, -91, 103, 22, -34, 224, -10, -218, -135, 79, -16, -28, -164, 92,
  118, 30, -3, -118, -154, 1, -13, -48, -30, 9, -72, -77, -43, 139, 186,
  128, 9, 82, 83, -96, 215, 194, 154, 95, 280, -84, 139, -143, 126, -61, 2,
  137, -9, 188, 27, 55, 27, -10, -2, 68, 222, 6]

theorem fractionalNearFrameSubtreeG2R0323_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0323Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0323Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0323Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0323_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0323LowerBoundTable : List ℤ :=
  [53, 257, 423, 368, -81, -34, 277, -109, -27, 254, 149, 543, -315, 361,
  47, 455, 106, 491, 230, 387, 91, 70, 65, 474, -27]

def fractionalNearFrameSubtreeG2R0323LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0323Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0323LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
