import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0040`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0040Mask : ℕ := 538377142837836

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0040Witness : Array ℤ :=
  #[52, 34, -34, 46, -32, 55, -14, 33, -42, -80, -28, 37, 6, -36, 19, 5,
  -72, -38, -70, 39, 79, 60, 29, 15, 57, 119, -18, 24, 39, -21, 41, -10,
  -79, -95, 101, 115, -129, -40, -92, 36, 37, 81, 1, -7, 60, 61, 78, 11,
  -61, -35, -11, 55, -35, -3, 14, -105, -69, -18, 68, 141, 55, -20, 108, 13,
  -71, -68, 40, -46, 8, 28, 32, -11, -16, -32, -48, 12, 59, -19, -5, 21,
  -14, 44, 88, 29, -3, 148, -41, -12, -11, 40, 94, -69, 4, 27, 32, 125, -10,
  -7, 21, 10, 28, 44, 10, 0, 13, 35, 48, -52, -23, -13, 72, 82, 65, -1, -46,
  -60, -23, -33, -87, -106, -60, 36, 119, -31, 52, -62, 29, 48, -13, -28,
  15, 25, 21, -3, -54, 27, 49, -57, 36, 3, 66, 2, 59, 112, 81, 75, 80, 63,
  16, 66, 47, 96, 89, 97, -52, 1, 29, 23, 85, -43, -88, 12, -8, -35, -50,
  -4, 31, 50]

theorem fractionalNearFrameSubtreeG1R0040_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0040Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0040Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0040Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0040_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0040LowerBoundTable : List ℤ :=
  [49, 205, 11, 51, 201, 182, 82, 137, 160, 270, 124, 193, 220, 173, 161,
  125, -32, 232, -43, 97, 99, 320, 496, 10, 285]

def fractionalNearFrameSubtreeG1R0040LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0040Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0040LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
