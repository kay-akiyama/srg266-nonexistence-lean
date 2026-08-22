import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0034`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0034Mask : ℕ := 1391258324418819

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0034Witness : Array ℤ :=
  #[-38, 62, -55, 31, 10, -67, 16, 7, -176, 0, -7, 66, 61, 108, 55, 108,
  101, 29, 68, 54, 71, -25, -65, 23, -276, 28, -77, 0, 111, -22, -26, -52,
  -41, -65, 51, -111, 39, -6, 74, 63, 6, -58, 0, 32, 127, -130, -46, -91,
  30, -39, -10, 49, 122, -53, 91, 54, 31, -23, 34, -83, 101, 87, 95, -46,
  19, -33, 12, 28, 34, 43, 31, 40, 60, -40, 58, 53, 78, -46, -60, -19, -67,
  -27, -24, -3, -16, 8, -61, 66, -70, -87, 37, -47, -36, -75, 33, 109, 117,
  -42, 70, -61, 90, -59, -16, 104, -33, 163, -9, 59, -176, 91, 42, 73, 28,
  85, 55, -54, -29, 85, 88, 9, 47, 1, 67, -104, -80, -9, -23, 1, -33, -63,
  42, 75, -41, 75, -159, 140, -138, 79, 100, 86, 74, 44, 113, 0, -26, 89, 9,
  -104, 125, -54, 103, 46, -36, -60, 47, 176, -100, -35, 4, -14, 22, 124,
  -81, 53, -40, 18, -81, 1]

theorem fractionalNearFrameSubtreeG5R0034_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0034Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0034Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0034Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0034_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0034LowerBoundTable : List ℤ :=
  [34, 119, 63, 3, 39, 121, 96, -81, 272, 40, 490, 83, 591, 423, -7, -112,
  124, -106, 84, 338, -155, 169, 226, 308, 415]

def fractionalNearFrameSubtreeG5R0034LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0034Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0034LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
