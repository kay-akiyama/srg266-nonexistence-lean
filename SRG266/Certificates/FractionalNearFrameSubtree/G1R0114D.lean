import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0114`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0114Mask : ℕ := 969037795673164

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0114Witness : Array ℤ :=
  #[86, -106, -50, -9, -31, 108, -40, -24, -26, -122, 30, 181, 150, 30, 114,
  -85, -66, -35, -109, -53, 71, 34, 46, 89, 30, 1, 90, 138, 70, 40, 76, 184,
  -227, -166, 51, 221, -217, -46, -225, 59, 135, 112, -15, -20, 62, -45,
  133, -30, -49, 68, 146, 59, -73, 105, -40, -253, 31, -127, 132, 289, -64,
  10, 270, 232, -8, 90, 35, -45, 20, 55, 60, -11, 19, 41, 59, 143, 16, -91,
  47, -49, 146, -6, 121, 25, 34, -25, -36, 24, -73, 82, -54, -9, 65, 68, 11,
  65, 136, -95, 36, -109, -28, 56, -135, 110, 31, 160, 98, 111, 192, 68, 0,
  -57, -32, 47, -97, -5, -95, 101, 53, 41, 47, 21, -28, -35, 48, -1, -98,
  -124, 64, 176, -55, -15, 158, 157, -70, 23, -65, 86, -10, 74, 60, -88,
  -26, 86, -64, -42, -17, -42, 59, 18, 97, 84, 35, 4, -50, -18, 165, -2,
  -67, -42, 56, -22, -80, -37, 95, 15, 25, -133]

theorem fractionalNearFrameSubtreeG1R0114_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0114Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0114Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0114Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0114_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0114LowerBoundTable : List ℤ :=
  [113, 37, 221, 218, 50, 431, 67, 323, 187, 503, -17, 341, 300, 793, 329,
  251, 104, 8, 42, 427, 560, 181, 10, 512, 402]

def fractionalNearFrameSubtreeG1R0114LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0114Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0114LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
