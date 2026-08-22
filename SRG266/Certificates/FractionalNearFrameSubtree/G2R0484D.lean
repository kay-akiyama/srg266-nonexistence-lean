import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0484`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0484Mask : ℕ := 5810613633589922

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0484Witness : Array ℤ :=
  #[-7, -54, 40, 49, -67, 76, 9, -8, 88, 146, -80, 76, -105, 92, 150, -8,
  104, 149, 302, -53, 4, -91, 76, -139, -105, -6, 53, 22, 120, -136, 50, 13,
  36, -36, 42, -51, -136, 130, 79, 65, -143, -133, -50, 2, 103, 84, 88, 12,
  -118, 36, 25, -34, -31, -9, 73, 106, 210, -78, 89, -60, 8, 0, -116, -118,
  59, -78, -47, 135, 36, -1, -57, 107, 104, -10, -52, 63, 65, 70, -51, -121,
  25, 90, 45, -41, -66, 54, -125, 33, 28, 1, -72, 83, 58, 40, 9, 79, 77,
  -42, -162, -28, -113, 61, 45, 125, 6, 111, -66, 46, 130, 25, -27, -56,
  -75, -4, 27, 52, 110, 13, 0, -72, 87, -46, 25, -73, 29, 86, 7, 165, 35,
  229, 135, 124, 91, 52, -170, 163, 16, 116, -34, 137, 63, -40, 55, 41, -97,
  -128, -8, -57, 105, 17, 84, 135, -119, 154, -12, 14, 156, -6, 120, 103,
  -92, 153, -38, -61, 37, 22, 159, 54]

theorem fractionalNearFrameSubtreeG2R0484_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0484Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0484Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0484Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0484_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0484LowerBoundTable : List ℤ :=
  [176, 412, 301, 367, 3, 203, 121, 163, 243, 481, 172, 755, 536, 25, 117,
  475, 109, -100, 176, 470, 637, 73, 136, 492, 106]

def fractionalNearFrameSubtreeG2R0484LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0484Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0484LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
