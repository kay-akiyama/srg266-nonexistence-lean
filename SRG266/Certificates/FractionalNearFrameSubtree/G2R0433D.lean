import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0433`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0433Mask : ℕ := 5785205406291468

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0433Witness : Array ℤ :=
  #[-32, -86, -150, -46, 3, 71, 58, 142, 93, 62, 168, 84, -14, 23, 75, -4,
  48, 65, 27, 105, 92, 68, -31, 30, -147, 132, 14, -24, -63, -18, -34, -44,
  45, 30, 78, -86, -92, -47, -3, 115, 153, 188, -76, -50, 29, 211, 56, -37,
  23, -11, -36, 8, 116, -65, -42, -147, 39, 141, 79, 98, 109, 14, 115, 124,
  68, -57, 69, 99, 89, 197, 54, -35, 101, 81, -145, 68, -41, 5, 50, -20,
  116, 35, 125, 19, -4, 51, 68, -22, 66, 68, 29, -14, 44, 19, 17, 169, 90,
  -54, -2, -54, 30, 37, 66, -123, 34, 9, 196, 96, -2, -159, 4, 24, -143,
  -12, -82, 0, 17, 54, 104, 128, 77, 155, 135, 33, 16, -102, 22, -79, -119,
  -10, -16, 38, -138, 104, 35, 128, 89, 14, 81, 200, 0, -7, -26, -90, -50,
  -20, -63, -128, -200, -20, 92, -7, 22, 31, 15, 67, 36, 53, -54, 0, 197,
  -10, -22, -62, 72, -116, 8, -50]

theorem fractionalNearFrameSubtreeG2R0433_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0433Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0433Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0433Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0433_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0433LowerBoundTable : List ℤ :=
  [227, 2, 208, 461, 158, 53, 337, 206, 462, -155, 147, 458, 193, 330, 90,
  23, 763, 296, 435, 510, 249, 264, 249, 584, 545]

def fractionalNearFrameSubtreeG2R0433LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0433Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0433LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
