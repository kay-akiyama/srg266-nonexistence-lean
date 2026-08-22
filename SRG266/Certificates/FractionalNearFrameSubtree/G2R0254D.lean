import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0254`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0254Mask : ℕ := 5356460395053644

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0254Witness : Array ℤ :=
  #[-36, -15, -1, 8, 0, 7, -22, -1, -28, -15, 53, 57, 7, 65, 74, 127, 16,
  33, 22, 23, 33, 37, 9, 37, 15, 87, -61, -19, 21, -37, 23, 66, 80, 22, -41,
  -17, 0, -37, 8, 0, 53, -1, 36, -47, 36, -71, 41, 15, 25, -12, 2, 17, 75,
  10, 24, 72, -39, 49, 19, 23, -32, 0, 32, -28, -35, 15, -107, -56, 21, 70,
  62, 45, 7, -16, 50, 122, 20, -2, -2, 46, 14, -70, 3, 42, 81, 15, -36, 21,
  -42, 9, -19, 7, -33, -6, -29, 1, 8, 6, 38, 15, -34, 14, -31, -14, 52, 13,
  71, -20, 42, -22, 57, 0, 38, 55, -14, 28, -57, 34, 73, 27, 22, -55, -13,
  55, 36, -14, 14, 15, -60, 25, 27, -40, 26, -47, -25, -75, 35, -22, 25, -1,
  53, 7, 20, 22, 42, 3, 41, -36, -55, -19, -15, -41, 0, 37, 51, 7, 0, -75,
  44, 53, -92, -35, 37, 32, 43, 9, -106, -41]

theorem fractionalNearFrameSubtreeG2R0254_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0254Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0254Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0254Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0254_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0254LowerBoundTable : List ℤ :=
  [68, 2, -22, 48, 108, 46, 94, 135, 151, -41, -2, 96, 225, 232, 229, 155,
  444, 200, 9, 156, 290, 74, 449, -51, 26]

def fractionalNearFrameSubtreeG2R0254LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0254Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0254LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
